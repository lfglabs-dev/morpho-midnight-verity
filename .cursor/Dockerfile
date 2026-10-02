FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git python3 python3-venv build-essential unzip zstd sudo ripgrep \
    && rm -rf /var/lib/apt/lists/*
RUN id -u ubuntu >/dev/null 2>&1 || useradd -m -s /bin/bash ubuntu
RUN echo 'ubuntu ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/ubuntu
USER ubuntu
ENV ELAN_HOME=/home/ubuntu/.elan
ENV PATH=/home/ubuntu/.elan/bin:$PATH
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/v4.1.2/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.31.0 \
    && rm /tmp/elan-init.sh \
    && lean --version && lake --version
USER root
RUN printf '%s\n' 'morpho-lean-v4.31.0' > /etc/morpho-proof-environment
USER ubuntu
