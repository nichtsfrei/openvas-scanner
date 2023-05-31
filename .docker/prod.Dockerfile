ARG VERSION=unstable
# this allows to work on forked repository
ARG REPOSITORY=greenbone/openvas-scanner

FROM greenbone/openvas-smb AS openvas-smb

FROM greenbone/gvm-libs:$VERSION AS build
COPY . /source
RUN apt-get update && apt-get install --no-install-recommends --no-install-suggests -y \
    ca-certificates\
  libpcap-dev libssh-dev zlib1g-dev \
    curl
RUN curl -sSf https://sh.rustup.rs -o wtf.sh
RUN sh wtf.sh --default-toolchain stable -y
ENV PATH=/root/.cargo/bin:$PATH
RUN cargo --version
RUN sh /source/.github/install-openvas-dependencies.sh
COPY --from=openvas-smb /usr/local/lib/ /usr/local/lib/
RUN cmake -DCMAKE_BUILD_TYPE=Release -DINSTALL_OLD_SYNC_SCRIPT=OFF -B/build /source
RUN DESTDIR=/install cmake --build /build -- install
# TODO find another less scripty way to install that
WORKDIR /source/rust
RUN cargo build --release
RUN mv /source/rust/target/release/nasl-cli /install/usr/local/bin/nasl-cli


FROM greenbone/gvm-libs:$VERSION
ARG TARGETPLATFORM
RUN apt-get update && apt-get install --no-install-recommends --no-install-suggests -y \
  bison \
  libjson-glib-1.0-0 \
  libksba8 \
  nmap \
  libcap2-bin \
  snmp \
  netdiag \
  pnscan \
  libbsd0 \
  rsync \
  # net-tools is required by some nasl plugins.
  # nasl_pread: Failed to execute child process “netstat” (No such file or directory)
  net-tools \
  # for openvas-smb support
  python3-impacket \
  libgnutls30 \
  libgssapi3-heimdal \
  libkrb5-26-heimdal \
  libasn1-8-heimdal \
  libroken18-heimdal \
  libhdb9-heimdal \
  libpopt0 \
  zlib1g-dev \
  && rm -rf /var/lib/apt/lists/*
COPY .docker/openvas.conf /etc/openvas/
COPY --from=build /install/ /
COPY --from=openvas-smb /usr/local/lib/ /usr/local/lib/
COPY --from=openvas-smb /usr/local/bin/ /usr/local/bin/
RUN ldconfig
# allow openvas to access raw sockets and all kind of network related tasks
RUN setcap cap_net_raw,cap_net_admin+eip /usr/local/sbin/openvas
# allow nmap to send e.g. UDP or TCP SYN probes without root permissions
ENV NMAP_PRIVILEGED=1
RUN setcap cap_net_raw,cap_net_admin,cap_net_bind_service+eip /usr/bin/nmap
