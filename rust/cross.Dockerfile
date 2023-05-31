FROM ghcr.io/cross-rs/x86_64-unknown-linux-gnu:latest
RUN apt-get update && apt-get install -y \
  libpcap-dev libssh-dev zlib1g-dev
