# z3 examples

This repository principally contains examples for a tutorial presentation at [the Stony Brook 2022 Workshop on Model Theoretic Representations in Phonology](https://www.jeffreyheinz.net/events/WMTRPprogram.html).


## SMTLIB scripts

If you want to run these locally (and follow the tutorial), you will need `z3` installed and available on your path.

Once you are in a terminal and have navigated to this directory (`.../stuttering-banjo`), simply pass the script as an argument to `z3`. For example,
```
> z3 ex1.smt
sat
(
  (define-fun p () Bool
    true)
  (define-fun q () Bool
    false)
  (define-fun r () Bool
    false)
)
```

*Alternatively*, you can (per the workshop tutorial) copy/paste script contents into the [z3 Playground](https://microsoft.github.io/z3guide/Freeform%20Editing/). This will allow you to skip any difficulties with installation. Note that some scripts may contain options that may not be available with however Microsoft Research has configured the (new and still evolving, as of summer 2022) "Z3 Guide" codeboxes.


## Simple Python example(s)

You will need `z3` installed and the *official* Python bindings package installed (`z3-solver`; see the instructions in the `z3` GitHub repository).

Once your are in the terminal and have navigated to this directory (`.../stuttering-banjo`), simply pass the script as an argument to z3. For example,
```
> python ex1.py
sat
[p = True, q = False, r = False]
```

## Wolof harmony / Doyle et al. (2014)

The directory `wolof-doyle-et-al-2014` contains a Jupyter notebook in two file formats. I suggest opening the `.html` example; GitHub should be able to render the file just fine if you open the file while browsing this repository from your web browser.

The notebook documents an early attempt (2018?) I made at evaluating the usability of `z3` --- crucially without really knowing much at the time about `z3` --- by seeing if I could use `z3` (accessed through [Rosette](https://emina.github.io/rosette/), though I don't think I actually used any particularly advanced features of Rosette *per se* over and above what I could have accomplished in `z3` via e.g. Python bindings) to replicate Harmonic Grammar / MaxEnt OT analyses of simplified Wolof harmony described in [Doyle et al. (2014)](https://pages.ucsd.edu/~gdoyle/papers/doyle-et-al-2014-acl.pdf).

The notebook may be difficult to follow in detail if you are not familiar with the basic idioms of functional programming or Lisp syntax. Nevertheless, I have tried to document as much relevant context within the notebook as I practically could at the time I made it (2018).

If you are interested in running this notebook interactively (rather than just looking at a static `html` file), contact me and I will be happy to help you and/or add more instructions/configuration files to help set up an environment that includes a Racket/Rosette kernel for Jupyter.
Alternatively, you might consider as an exercise trying to replicate what I did in your language of choice (probably Python) using `z3` (i.e. without Rosette as a wrapper/intermediary).
