Martin Escardo 2011.

The Cantor space is the type (ℕ → 𝟚). We show it is compact, under
the assumptions discussed in CountableTychonoff.

This module is a set of corollaries of the module CountableTychonoff
and other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Two
open import UF-FunExt

module CantorCompact (fe : ∀ 𝓤 𝓥 → funext 𝓤 𝓥) where

open import CompactTypes
open import CountableTychonoff (fe)
open import CompactTypes
open import WeaklyCompactTypes

cantor-compact∙ : compact∙ (ℕ → 𝟚)
cantor-compact∙ = countable-Tychonoff (λ i → 𝟚-compact∙)

cantor-compact : compact (ℕ → 𝟚)
cantor-compact = compact∙-gives-compact cantor-compact∙

cantor-wcompact : wcompact (ℕ → 𝟚)
cantor-wcompact = compact-gives-wcompact cantor-compact∙

\end{code}

The characteristic function of the universal quantifier
of the Cantor space:

\begin{code}

A : ((ℕ → 𝟚) → 𝟚) → 𝟚
A = pr₁(wcompact-implies-wcompact' cantor-wcompact)

\end{code}

Discreteness of ((ℕ → 𝟚) → ℕ):

\begin{code}

open import DiscreteAndSeparated

discrete-Cantor→ℕ : discrete((ℕ → 𝟚) → ℕ)
discrete-Cantor→ℕ = compact-discrete-discrete' (fe 𝓤₀ 𝓤₀) cantor-compact ℕ-discrete

\end{code}

The characteristic function of equality on ((ℕ → 𝟚) → ℕ):

\begin{code}

open import DecidableAndDetachable

equal : ((ℕ → 𝟚) → ℕ) → ((ℕ → 𝟚) → ℕ) → 𝟚

equal f  = pr₁(characteristic-function(discrete-Cantor→ℕ f))

\end{code}

Experiments: Evaluate the following to normal form (give ₀, ₁, ₁, ₀ quickly):

\begin{code}

number : 𝟚 → ℕ
number ₀ = 0
number ₁ = 1

test0 : 𝟚
test0 = A(λ α → min𝟚(α 17)(α 180))

test1 : 𝟚
test1 = A(λ α → ₁)

test2 : 𝟚
test2 = equal (λ α → number(α 17)) (λ α → number(α 100))

test3 : 𝟚
test3 = equal (λ α → number(α 100)) (λ α → number(α 100))

test4 : 𝟚
test4 = equal (λ α → number(α 1000)) (λ α → number(α 1000))

test5 : 𝟚
test5 = equal (λ α → number(α 1001)) (λ α → number(α 1000))

\end{code}
