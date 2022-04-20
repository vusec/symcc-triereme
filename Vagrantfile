# -*- mode: ruby -*-
# vi: set ft=ruby :

Vagrant.configure("2") do |config|
  config.vm.box = "ubuntu/focal64"

  config.vm.provision "shell", inline: <<-SHELL
    set -euo pipefail

    apt-get update
    apt-get upgrade -y

    apt-get install -y \
        git \
        cargo \
        clang-10 \
        cmake \
        g++ \
        git \
        libz3-dev \
        llvm-10-dev \
        llvm-10-tools \
        ninja-build \
        python2 \
        python3-pip \
        zlib1g-dev

    python3 -m pip install lit
  SHELL
end
