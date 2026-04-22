## Toolchain

- Rocq/Coq: `9.1.0`
- OCaml: `5.2.1`
- `coq-record-update`: `0.3.4`

## Build (current Make-based workflow)

1. Generate the Makefile:
   ```sh
   coq_makefile -f _CoqProject -o Makefile
   ```
2. Build:
   ```sh
   make -j"$(sysctl -n hw.ncpu)"
   ```

## Build with dune (recommended)

```sh
dune build -j"$(sysctl -n hw.ncpu)"
```

## Reproducible setup with opam

This repository includes `pico-coq.opam` so dependencies can be installed in an
isolated switch.

```sh
# From the repo root
opam switch create . 5.2.1
eval "$(opam env)"

# Pin this package and install only its dependencies
opam pin add . -n
opam install . --deps-only

# Build (dune)
dune build -j"$(sysctl -n hw.ncpu)"
```

## Notes

- `dune` and `_CoqProject` builds are both available during transition.
- The opam package build uses `dune build`.
