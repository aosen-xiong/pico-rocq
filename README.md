## Known Workable Versions with coq

- Rocq 9.1.0
- Ocaml 5.2.1

## Dependency required

- coq-record-update 0.3.4 https://github.com/tchajed/coq-record-update

## How to Build the Project

1. Generate the Makefile:
   ```sh
   coq_makefile -f _CoqProject -o Makefile
   ```
2. Build the project:
   ```sh
   make
   ```
## TODO
1. adapted substitution/framing preserve wf_r_config lemma
2. 