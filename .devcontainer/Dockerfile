FROM ocaml/opam:debian-12-ocaml-5.4

# System packages needed to build fiat-crypto + run Claude Code
USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential \
      m4 \
      git \
      pkg-config \
      libgmp-dev \
      curl \
      ca-certificates \
      python3 \
      time \
      zsh \
      less \
      vim-tiny \
    && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

# Claude Code CLI (global npm install)
RUN npm install -g @anthropic-ai/claude-code

# Back to the non-root opam user that owns the opam switch
USER opam
WORKDIR /home/opam

# Create a switch pinned to OCaml 5.4.0 (matching the host) so .vo files
# are interchangeable between host and container.
RUN opam switch create 5.4.0 ocaml-base-compiler.5.4.0

# Install Rocq/Coq 9.0 and build tooling.
# The project's own dependencies (coqprime, rewriter, rupicola, bedrock2)
# come from git submodules and are built by `make deps`, so we only need
# the compiler + stdlib here.
RUN opam update && \
    opam install -y dune rocq-core.9.0.0 rocq-stdlib.9.0.0 coq-core.9.0.0 coq-stdlib.9.0.0 && \
    opam clean -a

# Make opam env available in every shell (interactive + login)
RUN echo 'eval $(opam env --switch=5.4.0)' >> /home/opam/.bashrc && \
    echo 'eval $(opam env --switch=5.4.0)' >> /home/opam/.zshrc 2>/dev/null || true

WORKDIR /workspace
CMD ["/bin/zsh"]
