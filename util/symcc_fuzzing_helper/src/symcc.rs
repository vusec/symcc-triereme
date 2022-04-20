// This file is part of SymCC.
//
// SymCC is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// SymCC is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// SymCC. If not, see <https://www.gnu.org/licenses/>.

use anyhow::{bail, ensure, Context, Result};
use regex::Regex;
use serde::Serializer;
use std::collections::HashSet;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::{self, Read};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::str;
use std::time::{Duration, Instant};

const TIMEOUT: u32 = 90;

/// Replace the first '@@' in the given command line with the input file.
fn insert_input_file<S: AsRef<OsStr>, P: AsRef<Path>>(
    command: &[S],
    input_file: P,
) -> Vec<OsString> {
    let mut fixed_command: Vec<OsString> = command.iter().map(|s| s.into()).collect();
    if let Some(at_signs) = fixed_command.iter_mut().find(|s| *s == "@@") {
        *at_signs = input_file.as_ref().as_os_str().to_os_string();
    }

    fixed_command
}

/// Score of a test case.
///
/// We use the lexical comparison implemented by the derived implementation of
/// Ord in order to compare according to various criteria.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
struct TestcaseScore {
    /// First criterion: new coverage
    new_coverage: bool,

    /// Second criterion: being derived from seed inputs
    derived_from_seed: bool,

    /// Third criterion: size (smaller is better)
    file_size: i128,

    /// Fourth criterion: name (containing the ID)
    base_name: OsString,
}

impl TestcaseScore {
    /// Score a test case.
    ///
    /// If anything goes wrong, return the minimum score.
    fn new(t: impl AsRef<Path>) -> Self {
        let size = match fs::metadata(&t) {
            Err(e) => {
                // Has the file disappeared?
                log::warn!(
                    "Warning: failed to score test case {}: {}",
                    t.as_ref().display(),
                    e
                );

                return TestcaseScore::minimum();
            }
            Ok(meta) => meta.len(),
        };

        let name: OsString = match t.as_ref().file_name() {
            None => return TestcaseScore::minimum(),
            Some(n) => n.to_os_string(),
        };
        let name_string = name.to_string_lossy();

        TestcaseScore {
            new_coverage: name_string.ends_with("+cov"),
            derived_from_seed: name_string.contains("orig:"),
            file_size: -i128::from(size),
            base_name: name,
        }
    }

    /// Return the smallest possible score.
    fn minimum() -> TestcaseScore {
        TestcaseScore {
            new_coverage: false,
            derived_from_seed: false,
            file_size: std::i128::MIN,
            base_name: OsString::from(""),
        }
    }
}

/// A directory that we can write test cases to.
pub struct TestcaseDir {
    /// The path to the (existing) directory.
    pub path: PathBuf,
    /// The next free ID in this directory.
    current_id: u64,
}

impl TestcaseDir {
    /// Create a new test-case directory in the specified location.
    ///
    /// The parent directory must exist.
    pub fn new(path: impl AsRef<Path>) -> Result<TestcaseDir> {
        let dir = TestcaseDir {
            path: path.as_ref().into(),
            current_id: 0,
        };

        fs::create_dir(&dir.path)
            .with_context(|| format!("Failed to create directory {}", dir.path.display()))?;
        Ok(dir)
    }
}

/// Copy a test case to a directory, using the parent test case's name to derive
/// the new name.
pub fn copy_testcase(
    testcase: impl AsRef<Path>,
    target_dir: &mut TestcaseDir,
    parent: impl AsRef<Path>,
    relative_time: u64,
) -> Result<()> {
    let orig_name = parent
        .as_ref()
        .file_name()
        .expect("The input file does not have a name")
        .to_string_lossy();
    ensure!(
        orig_name.starts_with("id:"),
        "The name of test case {} does not start with an ID",
        parent.as_ref().display()
    );

    if let Some(orig_id) = orig_name.get(3..9) {
        let new_name = format!(
            "id:{:06},src:{},time:{}",
            target_dir.current_id, &orig_id, relative_time
        );
        let target = target_dir.path.join(new_name);
        log::debug!("Creating test case {}", target.display());
        fs::copy(testcase.as_ref(), target).with_context(|| {
            format!(
                "Failed to copy the test case {} to {}",
                testcase.as_ref().display(),
                target_dir.path.display()
            )
        })?;

        target_dir.current_id += 1;
    } else {
        bail!(
            "Test case {} does not contain a proper ID",
            parent.as_ref().display()
        );
    }

    Ok(())
}

/// Information on the run-time environment.
///
/// This should not change during execution.
#[derive(Debug)]
pub struct AflConfig {
    /// The command that AFL uses to invoke the target program.
    target: OsString,

    /// The args that AFL uses to invoke the target program.
    target_args: Vec<OsString>,

    /// The fuzzer instance's queue of test cases.
    queue: PathBuf,
}

impl AflConfig {
    /// Read the AFL configuration from a fuzzer instance's output directory.
    pub fn load(fuzzer_output: impl AsRef<Path>) -> Result<Self> {
        let afl_stats_file_path = fuzzer_output.as_ref().join("fuzzer_stats");
        let mut afl_stats_file = File::open(&afl_stats_file_path).with_context(|| {
            format!(
                "Failed to open the fuzzer's stats at {}",
                afl_stats_file_path.display()
            )
        })?;
        let mut afl_stats = String::new();
        afl_stats_file
            .read_to_string(&mut afl_stats)
            .with_context(|| {
                format!(
                    "Failed to read the fuzzer's stats at {}",
                    afl_stats_file_path.display()
                )
            })?;
        let afl_command: Vec<_> = afl_stats
            .lines()
            .find(|&l| l.starts_with("command_line"))
            .expect("The fuzzer stats don't contain the command line")
            .splitn(2, ':')
            .nth(1)
            .expect("The fuzzer stats follow an unknown format")
            .trim()
            .split_whitespace()
            .collect();

        let mut afl_target_command: Vec<_> = afl_command
            .iter()
            .skip_while(|s| **s != "--")
            .skip(1)
            .map(OsString::from)
            .collect();
        let target_args = afl_target_command.split_off(1);

        Ok(AflConfig {
            target: afl_target_command.pop().unwrap(),
            target_args,
            queue: fuzzer_output.as_ref().join("queue"),
        })
    }

    /// Return the most promising unseen test case of this fuzzer.
    pub fn best_new_testcase(&self, seen: &HashSet<PathBuf>) -> Result<(Option<PathBuf>, u64)> {
        let candidates: Vec<_> = fs::read_dir(&self.queue)
            .with_context(|| {
                format!(
                    "Failed to open the fuzzer's queue at {}",
                    self.queue.display()
                )
            })?
            .collect::<io::Result<Vec<_>>>()
            .with_context(|| {
                format!(
                    "Failed to read the fuzzer's queue at {}",
                    self.queue.display()
                )
            })?
            .into_iter()
            .map(|entry| entry.path())
            .filter(|path| path.is_file() && !seen.contains(path))
            .collect();

        let num_candidates = candidates.len() as u64;

        let best = candidates
            .into_iter()
            .max_by_key(|path| TestcaseScore::new(path));

        Ok((best, num_candidates))
    }

    pub fn get_target(&self) -> &OsString {
        &self.target
    }

    pub fn get_args(&self) -> &[OsString] {
        &self.target_args
    }
}

/// The run-time configuration of SymCC.
#[derive(Debug)]
pub struct SymCC {
    /// Do we pass data to standard input?
    use_standard_input: bool,

    /// The cumulative bitmap for branch pruning.
    bitmap: PathBuf,

    /// The place to store the current input.
    input_file: PathBuf,

    /// The command to run.
    command: Vec<OsString>,
}

fn serialize_duration_micros<S>(duration: &Duration, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_u128(duration.as_micros())
}

#[derive(serde::Serialize, Default, PartialEq, Eq, Debug)]
pub struct QSymStats {
    pub testcase: String,
    #[serde(rename = "total_time_us", serialize_with = "serialize_duration_micros")]
    pub total_time: Duration,
    #[serde(rename = "push_time_us", serialize_with = "serialize_duration_micros")]
    pub push_time: Duration,
    #[serde(rename = "pop_time_us", serialize_with = "serialize_duration_micros")]
    pub pop_time: Duration,
    #[serde(rename = "reset_time_us", serialize_with = "serialize_duration_micros")]
    pub reset_time: Duration,
    #[serde(
        rename = "assert_time_us",
        serialize_with = "serialize_duration_micros"
    )]
    pub assert_time: Duration,
    #[serde(rename = "check_time_us", serialize_with = "serialize_duration_micros")]
    pub check_time: Duration,
    pub killed: bool,
    pub unsat_count: u64,
    pub sat_count: u64,
    pub unknown_count: u64,
}

impl QSymStats {
    pub fn from_log_entry(log_entry: &str, testcase: String, killed: bool) -> Option<Self> {
        let re = Regex::new(concat!(
            r#"\{ "total_time": (\d+)"#,
            r#", "push_time": (\d+)"#,
            r#", "pop_time": (\d+)"#,
            r#", "reset_time": (\d+)"#,
            r#", "assert_time": (\d+)"#,
            r#", "check_time": (\d+)"#,
            r#", "unsat_count": (\d+)"#,
            r#", "sat_count": (\d+)"#,
            r#", "unknown_count": (\d+)"#,
            r#" \}"#
        ))
        .unwrap();

        let captures = re.captures(log_entry)?;

        let total_time = Duration::from_micros(captures[1].parse().unwrap());
        let push_time = Duration::from_micros(captures[2].parse().unwrap());
        let pop_time = Duration::from_micros(captures[3].parse().unwrap());
        let reset_time = Duration::from_micros(captures[4].parse().unwrap());
        let assert_time = Duration::from_micros(captures[5].parse().unwrap());
        let check_time = Duration::from_micros(captures[6].parse().unwrap());
        let unsat_count = captures[7].parse().unwrap();
        let sat_count = captures[8].parse().unwrap();
        let unknown_count = captures[9].parse().unwrap();

        Some(Self {
            testcase,
            total_time,
            push_time,
            pop_time,
            reset_time,
            assert_time,
            check_time,
            unsat_count,
            sat_count,
            unknown_count,
            killed,
        })
    }

    pub fn get_solver_time(&self) -> Duration {
        self.push_time + self.pop_time + self.reset_time + self.assert_time + self.check_time
    }
}

/// The result of executing SymCC.
pub struct SymCCResult {
    /// The generated test cases.
    pub test_cases: Vec<PathBuf>,
    /// Whether the process was killed (e.g., out of memory, timeout).
    pub killed: bool,
    /// The total time taken by the execution.
    pub time: Duration,
    /// Statistics reported by the QSYM backend
    pub qsym_stats: Option<QSymStats>,
}

impl SymCC {
    /// Create a new SymCC configuration.
    pub fn new(output_dir: PathBuf, command: &[String]) -> Self {
        let input_file = output_dir.join(".cur_input");

        SymCC {
            use_standard_input: !command.contains(&String::from("@@")),
            bitmap: output_dir.join("bitmap"),
            command: insert_input_file(command, &input_file),
            input_file,
        }
    }

    /// Try to extract the solver time from the logs produced by the Qsym
    /// backend.
    fn parse_qsym_stats(output: Vec<u8>, testcase: String, killed: bool) -> Option<QSymStats> {
        let qsym_stats_raw = output
            // split into lines
            .rsplit(|n| *n == b'\n')
            // convert to string
            .filter_map(|s| str::from_utf8(s).ok())
            // check that it's an SMT log line
            .find(|s| s.trim_start().starts_with("[STAT] SMT:"))?;

        // parse QSym stats
        QSymStats::from_log_entry(qsym_stats_raw, testcase, killed)
    }

    /// Run SymCC on the given input, writing results to the provided temporary
    /// directory.
    ///
    /// If SymCC is run with the Qsym backend, this function attempts to
    /// determine the time spent in the SMT solver and report it as part of the
    /// result. However, the mechanism that the backend uses to report solver
    /// time is somewhat brittle.
    pub fn run(
        &self,
        input: impl AsRef<Path>,
        output_dir: impl AsRef<Path>,
    ) -> Result<SymCCResult> {
        fs::copy(&input, &self.input_file).with_context(|| {
            format!(
                "Failed to copy the test case {} to our workbench at {}",
                input.as_ref().display(),
                self.input_file.display()
            )
        })?;

        fs::create_dir(&output_dir).with_context(|| {
            format!(
                "Failed to create the output directory {} for SymCC",
                output_dir.as_ref().display()
            )
        })?;

        let mut analysis_command = Command::new("timeout");
        analysis_command
            .args(&["-k", "5", &TIMEOUT.to_string()])
            .args(&self.command)
            .env("SYMCC_ENABLE_LINEARIZATION", "1")
            .env("SYMCC_AFL_COVERAGE_MAP", &self.bitmap)
            .env("SYMCC_OUTPUT_DIR", output_dir.as_ref())
            .stdout(Stdio::null())
            .stderr(Stdio::piped()); // capture SMT logs

        if self.use_standard_input {
            analysis_command.stdin(Stdio::piped());
        } else {
            analysis_command.stdin(Stdio::null());
            analysis_command.env("SYMCC_INPUT_FILE", &self.input_file);
        }

        log::debug!("Running SymCC as follows: {:?}", &analysis_command);
        let start = Instant::now();
        let mut child = analysis_command.spawn().context("Failed to run SymCC")?;

        if self.use_standard_input {
            io::copy(
                &mut File::open(&self.input_file).with_context(|| {
                    format!(
                        "Failed to read the test input at {}",
                        self.input_file.display()
                    )
                })?,
                child
                    .stdin
                    .as_mut()
                    .expect("Failed to pipe to the child's standard input"),
            )
            .context("Failed to pipe the test input to SymCC")?;
        }

        let result = child
            .wait_with_output()
            .context("Failed to wait for SymCC")?;
        let total_time = start.elapsed();
        let killed = match result.status.code() {
            Some(code) => {
                log::debug!("SymCC returned code {}", code);
                (code == 124) || (code == -9) // as per the man-page of timeout
            }
            None => {
                let maybe_sig = result.status.signal();
                if let Some(signal) = maybe_sig {
                    log::warn!("SymCC received signal {}", signal);
                }
                maybe_sig.is_some()
            }
        };

        let new_tests = fs::read_dir(&output_dir)
            .with_context(|| {
                format!(
                    "Failed to read the generated test cases at {}",
                    output_dir.as_ref().display()
                )
            })?
            .collect::<io::Result<Vec<_>>>()
            .with_context(|| {
                format!(
                    "Failed to read all test cases from {}",
                    output_dir.as_ref().display()
                )
            })?
            .iter()
            .map(|entry| entry.path())
            .collect();

        let qsym_stats = SymCC::parse_qsym_stats(
            result.stderr,
            input
                .as_ref()
                .file_name()
                .unwrap()
                .to_string_lossy()
                .to_string(),
            killed,
        );

        Ok(SymCCResult {
            test_cases: new_tests,
            killed,
            time: total_time,
            qsym_stats,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_score_ordering() {
        let min_score = TestcaseScore::minimum();
        assert!(
            TestcaseScore {
                new_coverage: true,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                derived_from_seed: true,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                file_size: -4,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                base_name: OsString::from("foo"),
                ..TestcaseScore::minimum()
            } > min_score
        );
    }

    #[test]
    fn test_solver_time_parsing() {
        let output = r#"This is SymCC running with the QSYM backend
Making data read from /tmp/yolo as symbolic
[STAT] SMT: { "total_time": 36088, "push_time": 0, "pop_time": 0, "reset_time": 20, "assert_time": 415, "check_time": 391, "unsat_count": 1, "sat_count": 2, "unknown_count": 3 }
[INFO] New testcase: /tmp/output/000000"#;

        assert_eq!(
            SymCC::parse_qsym_stats(output.as_bytes().to_vec(), "abc".to_string(), false),
            Some(QSymStats {
                testcase: String::from("abc"),
                total_time: Duration::from_micros(36088),
                push_time: Duration::from_micros(0),
                pop_time: Duration::from_micros(0),
                reset_time: Duration::from_micros(20),
                assert_time: Duration::from_micros(415),
                check_time: Duration::from_micros(391),
                killed: false,
                unsat_count: 1,
                sat_count: 2,
                unknown_count: 3,
            })
        );
    }
}
