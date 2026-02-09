---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
---

# Arithmetic Progressions - Almost Periodicity

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the exposition of Bloom and
Sisask on the Kelley-Meka bound on Roth numbers [2302.07211](https://arxiv.org/abs/2302.07211).

The main result is that there is some constant `c > 0` such that, if `A ⊆ {1, ..., N}` contains no
non-trivial arithmetic progression of length 3, then `|A| ≤ N/exp(c * (log n)^(1/12)))` for some
constant `c > 0`. This is an amazing improvement over previous bounds, which were all of the form
`N/(log n)^c` for some constant `c`.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed at AWS and Microsoft Research by Leonardo de Moura and his team.

## Content of this project

This project currently contains about 3k lines of Lean code about the discrete (difference)
convolution, discrete Lp norms, discrete Fourier transform. It also contains proofs of a version of
almost periodicity and of a quantitative version of the Marcinkiewicz-Zygmund inequality.

Once finished, this project will contain two main results (here `R` is the Roth number, the maximum
size of a set without three term arithmetic progressions):
* The **finite field case**: A proof that `R(F_q^n) ≤ q ^ (n - c * n ^ (1/9))` for some constant
  `c`. This is worse than the Ellenberg-Gijswijt bound `R(F_q^n) ≤ q ^ (n - c * n)` which was
  formalised in [Dahmen, Hölzl, Lewis](https://drops.dagstuhl.de/opus/volltexte/2019/11070/). The
  goal here is therefore not to improve on the existing bound but instead demonstrate the
  probability and Fourier analysis techniques, whereas Ellenberg-Gijswijt used the polynomial
  method.
* The **integer case**: A proof that `R(n) ≤ N/exp(c * (log n)^(1/9)))`, using the same techniques
  as in the finite field case, except for the fact that we now use Bohr sets instead of subspaces.
  This bound is a slight improvement over the Kelley-Meka bound (with `1/12` as the exponent instead
  of `1/9`). It is due to Bloom and Sisask.

### Code organisation

The Lean code is contained in the directory `LeanAPAP`. The subdirectories are:
* `Mathlib`: Material missing from existing mathlib developments
* `Prereqs`: New developments to be integrated to mathlib
* `Physics`: The physical (as opposed to Fourier space) proof steps that are shared
  between the finite field cases and integer case
* `FiniteField`: The proof steps specific to the finite field case
* `Integer`: The proof steps specific to the integer case

## What next?

Almost periodicity is nowadays a standard tool in additive combinatorics. The version we formalised is sufficient for many applications. In particular, it gives one of the best known bounds on Freiman's theorem. As a side goal, we might tackle Freiman's theorem.

The discrete convolution/Lp norm/Fourier transform material belongs in mathlib and we hope to PR it there soon. Almost periodicity should similarly be upstreamed to mathlib given the numerous applications. The rest of the material might forever live in this repository.

On top of the new developments, there are many basic lemmas needed for this project that are currently missing from mathlib.

See the [upstreaming dashboard](https://yaeldillies.github.io/apap/upstreaming) for more information.

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/apap)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

See instructions at https://github.com/PatrickMassot/leanblueprint/.

## Acknowledgements

Our project builds on mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)

## Source reference

`[BS]` : https://arxiv.org/abs/2302.07211

[BS]: https://arxiv.org/abs/2302.07211
