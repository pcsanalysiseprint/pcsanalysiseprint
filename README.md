# Impossibility Results for Post-Compromise Security in Real-World Communication Systems

This repository contains all formal models from the paper

`Impossibility Results for Post-Compromise Security in Real-World Communication Systems`

and the means to reproduce them.

## Structure

We provide the file `AbstractModel.m4` which can be converted into Tamarin files with the `m4` preprocessor.
For convenience, we provide a `makefile` which automatically calls m4 with the appropriate parameters to generate the different models we use throughout the paper.

The `makefile` supports the following commands:
* `make` // Builds all the models into their respective folders.
* `make proofs` // For each model, prove all automatically provable results.
* `make $(X)-model` // Build only the Tamarin file for model `X`.
* `make $(X)-proofs` // Prove all automatically provable results for model `X`.

Currently, valid model names are: `base`, `non-resilient-dyn`, `non-resilient-static`, `resilient-dyn`, `resilient-static`, `sequential-sessions`, and `proposal`.
Due to the time and resources the verification of the models can take, we recommend proving each of them individually.

After building the models, you can find the following folder structure:
```
├── base
│   ├── base.spthy
├── non-resilient-dyn
│   ├── non-resilient-dyn.spthy
├── non-resilient-static
│   ├── non-resilient-static.spthy
├── resilient-dyn
│   ├── resilient-dyn.spthy
├── resilient-static
│   ├── resilient-static.spthy
├── sequential
│   ├── sequential.spthy
├── proposal
│   ├── proposal.spthy
├── proofs
│   ├── ...
├── README.md
├── Makefile
├── TokenPassing.spthy
└── AbstractModel.m4
```
All directories but `proofs` are named after the corresponding models they contain. The `proofs` directory contains pre-computed proofs that were either manually created or take too long to reproduce easily.
The `TokenPassing.spthy` is a specialized version of the `sequential.spthy` model. It is not automatically generated from the `AbstractModel.m4`.

------

## Dependencies

### Tamarin Prover

We rely on the [Tamarin prover](https://tamarin-prover.com/) version 1.9.0. on the master branch

```
tamarin-prover 1.9.0, (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, 2010-2023

This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you
are welcome to redistribute it according to its LICENSE, see
'https://github.com/tamarin-prover/tamarin-prover/blob/master/LICENSE'.

maude tool: 'maude'
 checking version: 3.3. OK.
 checking installation: OK.
Generated from:
Tamarin version 1.9.0
Maude version 3.3
Git revision: ea7b979e436fc32f98369dd4e349fa0c6f1b1efd (with uncommited changes), branch: develop
Compiled at: 2024-07-10 11:47:09.315876473 UTC
```

Details regarding installation can be found on [Tamarin's webpage](https://tamarin-prover.com/manual/master/book/002_installation.html)

### M4 Preprocessor

We rely on the [M4 Preprocessor](https://www.gnu.org/software/m4/). It can either be downloaded and installed from its github source or via the package manager of your choice.

-------

## Summary of Results

| Model                	| Automatic   Lemmas 	| PCS (Proof) 	| PCS (CEX) 	|    Overall   	|
|----------------------	|:-------------------:	|:-----------:	|:---------:	|:------------:	|
| Base                 	|         ~9s         	|     ~51s    	|           	|      ~1m     	|
| Non-Resilient-Dyn    	|         ~9s         	|             	|           	|      ~9s     	|
| Non-Resilient-Static 	|         ~10s        	|             	|           	|     ~10s     	|
| Resilient-Dynamic    	|         ~9s         	|             	|   ~300s   	|     ~309s    	|
| Resilient-Static     	|         ~9s         	|             	|   ~333s   	|     ~342s    	|
| Sequential           	|         ~44s        	|     ~1h     	|           	|      ~1h     	|
| Tokenpassing         	|         ~27s        	|             	|   Manual  	| ~27s/ Manual 	|
| Proposal             	|         ~23s        	|     ~1h     	|           	|      ~1h     	|

---------------


## Instructions to Reproduce the Results

We run the full analysis on a ThinkPad X1 Carbon Gen 9 with 32Gb of RAM using a mixture of Tamarin's GUI, the command-line interface, and manual guidance.

For each model, we provide the previously mentioned `make` command to conveniently prove the statements that Tamarin can prove automatically. For instance, use
```
make non-resilient-dyn
```
to do so for the `non-resilient-dyn` model.

### Details on the Specifics of each Model
While the majority of our statements can be proven fully automatically, for some, we were only able to do so in the GUI of Tamarin by pressing 'a'. Note, that this is different from manually searching for the proof.
This is due to two reasons: 1) attempting the proof as a whole via the CLI can cause Tamarin to run out-of-memory, and 2) Tamarin's default search-strategy, i.e., iterative deepening depth-first search (IDDFS), can speed up exponentially if only a single proof step is saved. The second fact is due to the nature of IDDFS: Hitting the current bound shortly before finishing a proof (or finding a trace) will abort the search in this branch and first explore an exponential search-space in different branches.

We faced both issues when trying to prove our PCS properties. Tamarin's GUI let's us address both issues: By manually providing Tamarin with only the top-level case distinction of a proof, we were
able to automatically verify the property in each of the four cases by pressing 'a'. As a result, our proof for the PCS properties in the `sequential` model and the `proposal` model is cut into four files.

We will now give a quick overlook off each model.

#### Base
In this model, all statements can be proven fully automatic. To only prove the intermediate lemmas use `make base-proof`, and to also proof our Definition 5 and Definition 6, use `make base-pcs`.
The whole verification takes less than 1 minute.

#### Non-Resilient-Dyn
In this model, all statements can be proven fully automatic via `make non-resilient-dyn-proofs` in around 9 seconds.

#### Non-Resilient-Static
In this model, all statements can be proven fully automatic via `make non-resilient-dyn-proofs` in around 10 seconds.

#### Resilient-Dynamic
In this model, all statements can be proven fully automatic. In around 9 seconds, we can prove all intermediate statements via `make resilient-dyn-proofs`, and in around 300 seconds we can find the PCS counterexample via `make resilient-dyn-pcs`.

#### Resilient-Static
In this model, all statements can be proven fully automatic. In around 9 seconds, we can prove all intermediate statements via `make resilient-dyn-proofs`, and in around 333 seconds we can find the PCS counterexample via `make resilient-dyn-pcs`.

#### Sequential
In this model, all intermediate statements can be proven fully automatic in around 44 seconds via `make sequential-sessions-proofs`. To find the PCS counterexample we use Tamarin's GUI and perform a single case distinction manually followed by an automatic proof in each case. As described earlier, we've split the proof into one file per case of this top-level case distinction (4 files). We do this to avoid running out-of-memory and to provide easier way
of checking the proof. The respective files can be found in the `proofs` folder. The original runtime of this proof was around 1 hour. We were not able to prove PCS via the command-line interface.

#### Tokenpassing
In this model, all intermediate statements can be proven fully automatic in around 27 seconds via `make tokenpassing-proofs`. To find the trace for the PCS counterexample via `make resilient-dyn-pcs`, we manually
specified an ``exists-trace'' lemma which encodes the trace. In the `proofs` folder, we provide the corresponding `.spthy` file and a `.png` of the trace.

#### Proposal
In this model, all intermediate statements can be proven fully automatic in around 23 seconds via `make proposal-proofs`. As for the `sequential` model, we provide a partitioned proof in the `proofs` folder.
The original runtime of this proof was around 1 hour. We were not able to prove PCS via the command-line interface.
