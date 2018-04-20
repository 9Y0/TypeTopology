   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Martin Escardo, 2010--
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

   September 2017. This version removes the module CurryHoward, so
   that we use the symbols Σ and + rather than ∃ and ∨. This is to be
   compatible with univalent logic. We also make our development more
   compatible with the philosophy of univalent mathematics and try to
   streamline it a bit. The original version remains at
   http://www.cs.bham.ac.uk/~mhe/agda/ for the record and to avoid
   broken incoming links.

   December 2017. This version includes many new things, including a
   characterization of the injective types, which relies on the fact
   that the identity-type former Id_X : X → (X → U) is an embedding in
   the sense of univalent mathematics.

   January 2018. This again includes many new things, including
   𝟚-compactness, totally separated reflection, and how the notion of
   𝟚-compactness interacts with discreteness, total separatedess and
   function types. We apply these results to simple types.

   April 2018. The univalence foundations library was monolotic
   before. Now it it has been modularized.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

You can navigate this set of files by clicking at words or
symbols to get to their definitions.

The module dependency graph: http://www.cs.bham.ac.uk/~mhe/agda-new/manual.pdf

The following module investigates the notion of omniscience set. A
set X is omniscient iff

   (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁

\begin{code}

open import OmniscientTypes

\end{code}

The omniscience of ℕ is a contructive taboo, known as LPO, which is an
undecided proposition in our type theory. Nevertheless, we can show
that the function type LPO→ℕ is omniscient:

\begin{code}

open import LPO

\end{code}

See also:

\begin{code}

open import WLPO

\end{code}

An example of an omniscient set is ℕ∞, which intuitively (and under
classical logic) is ℕ ∪ { ∞ }, defined in the following module:

\begin{code}

open import GenericConvergentSequence 

\end{code}

But it is more direct to show that ℕ∞ is searchable, and get
omniscience as a corollary:

\begin{code}

open import SearchableTypes
open import ConvergentSequenceSearchable 

\end{code}

An interesting consequence of the omniscience of ℕ∞ is that the
following property, an instance of WLPO, holds constructively:

  (p : ℕ∞ → 𝟚) → ((n : ℕ) → p(under n) ≡ ₁) + ¬((n : ℕ) → p(under n) ≡ ₁).

where

  under : ℕ → ℕ∞

is the embedding. (The name for the embedding comes from the fact that
in published papers we used an underlined symbol n to denote the copy
of n : ℕ in ℕ∞.)

\begin{code}

open import ADecidableQuantificationOverTheNaturals

\end{code}

This is used to show that the non-continuity of a function ℕ∞ → ℕ is
decidable:

\begin{code}

open import DecidabilityOfNonContinuity

\end{code}

Another example of searchable set is the type of univalent
propositions (proved in the above module Searchable).

Given countably many searchable sets, one can take the disjoint sum
with a limit point at infinity, and this is again a searchable
sets. This construction is called the squashed sum of the countable
family searchable sets. It can be transfinitely iterated to produce
increasingly complex searchable ordinals.

\begin{code}

open import SquashedSum
open import SearchableOrdinals
open import LexicographicSearch
open import ConvergentSequenceInfSearchable

\end{code}

As a side remark, the following module characterizes ℕ∞ as the
final coalgebra of the functor 1+(-), and is followed by an
illustrative example:

\begin{code}

open import CoNaturals 
open import CoNaturalsExercise

\end{code}

The following module discusses in what sense ℕ∞ is the generic
convergent sequence, and proves that the universe U of types is
indiscrete, with a certain Rice's Theorem for the universe U as a
corollary:

\begin{code}

open import TheTopologyOfTheUniverse 
open import RicesTheoremForTheUniverse 

\end{code}

The following two rogue modules depart from our main philosophy of
working strictly within ML type theory with the propositional
axiom of extensionality. They disable the termination checker, for
the reasons explained in the first module. But to make our point,
we also include runnable experiments in the second module:

\begin{code}

open import CountableTychonoff 
open import CantorSearchable 

\end{code}

The following modules return to the well-behavedness paradigm.
The first one shows that a basic form of discontinuity is a
taboo. This, in fact, is used to formulate and prove Rice's
Theorem mentioned above:

\begin{code}

open import BasicDiscontinuityTaboo

\end{code}

The following shows that universes are injective, and more generally
that the injective types are the retracts of exponential powers of
universes:

\begin{code}

open import InjectiveTypes

\end{code}

This uses properties of products indexed by univalent propositions,
first that it is isomorphic to any of its factors:

\begin{code}

open import PropIndexedPiSigma

\end{code}

And, more subtly, that a product of searchable sets indexed by a
univalent proposition is itself searchable:

\begin{code}

open import PropTychonoff

\end{code}

And finally that the map Id {X} : X → (X → U) is an embedding in the
sense of univalent mathematics, where Id is the identity type former:

\begin{code}

open import IdEmbedding

\end{code}


The following generalizes the squashed sum, with a simple construction
and proof, using the injectivity of the universe and the Prop-Tychonoff theorem:

\begin{code}

open import ExtendedSumSearchable

\end{code}

The following modules define 𝟚-compactness and study its interaction
with discreteness and total separatedness, with applications to simple
types. We get properties that resemble those of the model of
Kleene-Kreisel continuous functionals of simple types, with some new
results.

\begin{code}

open import TotallySeparated
open import 2CompactTypes
open import SimpleTypes
open import FailureOfTotalSeparatedness 

\end{code}

The following modules contain auxiliary definitions and additional
results and discussion that we choose not to bring here:

\begin{code}

open import SpartanMLTT 
open import UF
open import UF2
open import DecidableAndDetachable 
open import DiscreteAndSeparated 
open import ExhaustibleTypes
open import Naturals 
open import BinaryNaturals
open import OrdinalCodes
open import Sequence
open import Two 
open import HiggsInvolutionTheorem
open import DummettDisjunction
open import UF-Choice
open import Dominance
open import KrausLemma
open import NonCollapsibleFamily
open import UnivalenceFromScratch
open import PlusOneLC
open import ArithmeticViaEquivalence
open import UAFE

\end{code}
