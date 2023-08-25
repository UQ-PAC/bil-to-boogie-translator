FROM ghcr.io/uq-pac/basil:latest as compiler-explorer
# https://github.com/madduci/docker-compiler-explorer/tree/master
RUN DEBIAN_FRONTEND=noninteractive apt-get update \
    && apt-get install -y curl \
    && curl -sL https://deb.nodesource.com/setup_18.x | bash - \
    && apt-get install -y \
        wget \
        ca-certificates \
        nodejs \
        make \
        git \
    && apt-get autoremove --purge -y \
    && apt-get autoclean -y \
    && rm -rf /var/cache/apt/* /tmp/* \
    && git clone https://github.com/ailrst/compiler-explorer.git /compiler-explorer \
    && cd /compiler-explorer \
    && echo "Add missing dependencies" \
    && npm i @sentry/node \
    && npm run webpack
WORKDIR /compiler-explorer
ENTRYPOINT [ "make" ]
CMD ["run"]

from compiler-explorer AS  ghcr.io/uq-pac/basil-compiler-explorer:latest
ADD basil-tool.py /compiler-explorer/basil-tool.py
RUN chmod +x /compiler-explorer/basil-tool.py
ADD basil.local.properties /compiler-explorer/etc/config/c.defaults.properties