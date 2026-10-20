# graph-theory-rocq Rocq 9.2 proof image, step (1) variant B2, DRAFT r0 (arthur, 2026-10-12). The recipe of
# environment/image/Dockerfile (graph-theory-rocq:2026-10-02) with: the 9.2 lock, coq-graph-theory pinned by path to
# upstream master 322e352b (UNRELEASED), rocq-mcp-evolve f5c3e30f, a build-limits assertion in every RUN, and records.
ARG BASE_IMAGE=ubuntu:24.04
ARG NODE_IMAGE=node:22-bookworm-slim
FROM ${NODE_IMAGE} AS node
FROM ${BASE_IMAGE}
SHELL ["/bin/bash", "-o", "pipefail", "-c"]
ARG DEBIAN_FRONTEND=noninteractive
ARG JOBS=2
ARG CLAUDE_VERSION=2.1.286
ARG CODEX_VERSION=0.159.2
ARG EXPECT_MEMORY_MAX=8589934592
ARG EXPECT_CPU_MAX="200000 100000"
ENV OPAMROOT=/opt/opam OPAMYES=1 OPAMROOTISOK=1
ENV PATH=/opt/opam/graph-theory-rocq/bin:/usr/local/bin:/usr/bin:/bin
ENV DISABLE_AUTOUPDATER=1
COPY assert-limits.sh /opt/gtrocq/assert-limits.sh
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl git jq libgmp-dev m4 opam \
    patch pkg-config python3 ripgrep rsync tini unzip xz-utils zlib1g-dev
COPY --from=node /usr/local/bin/node /usr/local/bin/node
COPY --from=node /usr/local/lib/node_modules/npm /usr/local/lib/node_modules/npm
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && ln -s /usr/local/lib/node_modules/npm/bin/npm-cli.js /usr/local/bin/npm \
 && ln -s /usr/local/lib/node_modules/npm/bin/npx-cli.js /usr/local/bin/npx \
 && npm install -g "@anthropic-ai/claude-code@${CLAUDE_VERSION}" "@openai/codex@${CODEX_VERSION}"
COPY opam-packages.lock /opt/gtrocq/opam-packages.lock
COPY sources/rocq-mcp-evolve.tar.gz /opt/gtrocq/rocq-mcp-evolve.tar.gz
COPY sources/graph-theory.tar.gz /opt/gtrocq/graph-theory.tar.gz
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && opam init --bare --disable-sandboxing --no-setup -y \
 && opam repo add rocq-released https://rocq-prover.org/opam/released --dont-select \
 && opam repo add coq-released https://coq.inria.fr/opam/released --dont-select \
 && opam switch create graph-theory-rocq ocaml-base-compiler.5.3.0 --no-switch \
      --repositories=rocq-released,coq-released,default -j "${JOBS}" \
 && mkdir /opt/gtrocq/graph-theory \
 && tar -xzf /opt/gtrocq/graph-theory.tar.gz -C /opt/gtrocq/graph-theory \
 && test -s /opt/gtrocq/graph-theory/coq-graph-theory.opam \
 && opam pin add --switch=graph-theory-rocq -n -k path coq-graph-theory.dev /opt/gtrocq/graph-theory \
 && mapfile -t packages < <(grep -v '^#' /opt/gtrocq/opam-packages.lock | sed '/^$/d') \
 && opam install --switch=graph-theory-rocq -j "${JOBS}" "${packages[@]}"
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && mkdir /opt/gtrocq/rocq-mcp-evolve \
 && tar -xzf /opt/gtrocq/rocq-mcp-evolve.tar.gz -C /opt/gtrocq/rocq-mcp-evolve \
 && test -s /opt/gtrocq/rocq-mcp-evolve/rocq-mcp-evolve.opam \
 && opam pin add --switch=graph-theory-rocq -n -k path rocq-mcp-evolve.dev /opt/gtrocq/rocq-mcp-evolve \
 && mapfile -t packages < <(grep -v '^#' /opt/gtrocq/opam-packages.lock | sed '/^$/d') \
 && opam install --switch=graph-theory-rocq -j "${JOBS}" rocq-mcp-evolve "${packages[@]}" \
 && test -x /opt/opam/graph-theory-rocq/bin/rocq-mcp-evolve
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && sha256sum /opt/gtrocq/rocq-mcp-evolve.tar.gz > /opt/gtrocq/rocq-mcp-source.sha256 \
 && sha256sum /opt/gtrocq/graph-theory.tar.gz > /opt/gtrocq/graph-theory-source.sha256 \
 && opam list --switch=graph-theory-rocq --installed --columns=name,version --short > /opt/gtrocq/installed-packages.txt \
 && opam switch export --switch=graph-theory-rocq --full /opt/gtrocq/linux-switch.export \
 && opam repo list --switch=graph-theory-rocq > /opt/gtrocq/opam-repositories.txt \
 && dpkg-query -W -f '${Package} ${Version}\n' > /opt/gtrocq/apt-packages.txt \
 && ocamlc -version && rocq --version && claude --version && codex --version
COPY kit/ /opt/gtrocq/
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && python3 /opt/gtrocq/check_versions.py \
 && chmod 755 /opt/gtrocq/entrypoint.sh /opt/gtrocq/smoke.sh \
 && chmod -R a+rX /opt/opam /opt/gtrocq \
 && if ! getent passwd 1000 >/dev/null; then useradd -m -u 1000 agent; fi \
 && mkdir -p /home/agent && chown 1000:1000 /home/agent
ENV HOME=/home/agent OPAMSWITCH=graph-theory-rocq
USER 1000:1000
WORKDIR /home/agent
# Install check (D7): the existing environment smoke (libraries load, MCP opens and closes a proof), as uid 1000 in a
# throwaway HOME, then the records into the build log. No corpus file is compiled.
RUN /bin/sh /opt/gtrocq/assert-limits.sh "$EXPECT_MEMORY_MAX" "$EXPECT_CPU_MAX" \
 && export HOME=/tmp/smoke-home && mkdir -p "$HOME" && cd /tmp \
 && /opt/gtrocq/entrypoint.sh /opt/gtrocq/smoke.sh \
 && rm -rf /tmp/smoke-home /tmp/gtrocq-smoke.* \
 && for f in installed-packages.txt opam-repositories.txt rocq-mcp-source.sha256 graph-theory-source.sha256; do \
      echo "== RECORD $f"; cat "/opt/gtrocq/$f"; done \
 && echo "== RECORD sha256" && sha256sum /opt/gtrocq/linux-switch.export /opt/gtrocq/apt-packages.txt /opt/gtrocq/opam-packages.lock \
 && echo "== RECORD uname $(uname -srm)"
ENTRYPOINT ["/usr/bin/tini", "--", "/opt/gtrocq/entrypoint.sh"]
CMD ["bash"]
