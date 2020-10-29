# Research code for the paper *Harmonic Syntax in Time: Rhythm Improves Grammatical Models of Harmony*

## Summary

This repository contains research code that was used to implement the computational experiments presented in the paper *Harmonic Syntax in Time: Rhythm Improves Grammatical Models of Harmony* by Daniel Harasim, Timothy J. O'Donnell, and Martin Rohrmeier.

The paper is archived on zenodo: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.3527812.svg)](https://doi.org/10.5281/zenodo.3527812)

## Usage

The code is provided as it is without any warranty. To compile the code, you can use the [Haskell programming language](https://www.haskell.org/) via the [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/).
- The computational experiments are implemented in the file `app/Main.hs`.
- The input data is stored in the directory `treebank`. A revised and extended version of this dataset was published in the paper [The Jazz Harmony Treebank](https://program.ismir2020.net/poster_2-06.html).
- The results of the experiments are stored in the files `harmonyRuleCounts.csv`, `ismirDataFinal.csv`, and `leftSplitProportions.csv`.
- The IPyhton notebook `ismir_data_viz.ipynb` implements statistical analyses and creates visualizations.

## Contact

Please contact daniel dot harasim at epfl dot ch if you have questions how to use this code.
