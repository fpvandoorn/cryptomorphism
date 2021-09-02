# Cryptomorphisms

Algorithms for automatically deriving cryptomorphisms between structures.
This is the code accompanying the paper and talk *Automating Concept Equivalence in Dependent Type Theory* at AITP 2021 by Floris van Doorn, Michael R. Douglas and David McAllester.

## Installation (Lean 3)

Instructions for running the Lean 3 code:

* Follow the [instructions](https://leanprover-community.github.io/get_started.html) under `Regular install` to get Lean and its tools.
* Download this repository
* On the command line, run `leanproject get-mathlib-cache` in your local copy of this repository to download the version of mathlib used by this repository (or if you don't have a local copy yet, run `leanproject get fpvandoorn/cryptomorphism` to clone and setup Lean).
* Browse the repository in VSCode by opening *the Lean 3 folder* in VSCode, e.g. `code lean3` (if you are in the `cryptomorphism` directory).

## Installation (Lean 4)

Instructions for running the Lean 4 code:

* Follow the [instructions](https://leanprover-community.github.io/get_started.html) under `Regular install` to get `elan` (you can ignore getting Python / mathlib tools).
* Download this repository
* You might need to run the following to set the default version of Lean 4 to use.
We will try to keep the code compiling with the latest Lean 4 nightly. If the code doesn't compile, try installing the `nightly` version from the date of the last commit.
```
elan install leanprover/lean4:nightly # (if this fails, close VSCode and try again)
elan default leanprover/lean4:nightly # this sets the default version of Lean used.
```
* Browse the repository in VSCode by opening *the Lean 4 folder* in VSCode, e.g. `code lean4` (if you are in the `cryptomorphism` directory).