# Call-by-Box Lambda Calculus — Agda Formalisation

This repository contains the Agda formalisation of the call-by-box lambda calculus (λ_b).
It includes the syntax, semantics and the call-by-box evaluation relation in λ_b as well as embeddings into λ_b. 
The formalisation depends on the standard library of Agda.

## Directory Structure
`formalisation/`
- `boxCalc.agda`: Contains the definition of \lterms in \lab, the definition of substitution and the definition of values in \lab.
- `boxCalcRed.agda`: Contains all the reduction relations in \lab.
- `calc.agda`: Contains the definition of \lterms in the standard \lc, the definition of substitution and the definition of values.
- `embedCBNIntoCBB.agda`: Contains the definition of Girard's embedding.
- `embedCBVIntoCBB.agda`: Contains the definition of Gödel's embedding.
- `nameCalcRed.agda`: Contains the reduction relations for \lan.
- `valueCalcRed.agda`: Contains the reduction relations for \lav.

`examples/` \
This directory contains examples to make the formalisation clearer. 

`proofs/` \
This directory contains some proofs of Girard's and Gödels' embeddings. 

## Dependencies
- Agda
- Agda Standard Library

Make sure the standard library is configured correctly.\
The installation guide for Agda and the standard library: https://agda.readthedocs.io/en/v2.8.0-rc2/getting-started/installation.html 

## Usage
You can load a file by opening it in Emacs with Agda's Emacs mode and pressing `C-c, C-l`

## Context

This repository contains the formalisation developed in the during the bachelor thesis:

**“Formalising Modal Embeddings of Call-by-Name and Call-by-Value”**  
submitted by Floris Reuvers, Computing Science, Radboud University, June 2025.

The project formalises the call-by-box lambda calculus (λ_b) and includes embeddings of call-by-name and call-by-value into λ_b.

Supervisor: dr. N.M. van der Weide \
Second assessor: dr. E.G.M. Hubbers