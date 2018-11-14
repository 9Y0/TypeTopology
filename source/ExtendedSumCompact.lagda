Martin Escardo 29 April 2014.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Embedding

module ExtendedSumCompact (fe : ∀ 𝓤 𝓥 → funext 𝓤 𝓥) where

open import CompactTypes
open import UF-InjectiveTypes (fe)
open import PropTychonoff (fe)

extended-sum-compact∙ : {X : 𝓤 ̇} {K : 𝓥 ̇} {Y : X → 𝓦 ̇} (j : X → K) → is-embedding j
                        → ((x : X) → compact∙(Y x)) → compact∙ K → compact∙(Σ(Y / j))
extended-sum-compact∙ j e ε δ = Σ-compact∙ δ (λ k → prop-tychonoff (e k) (ε ∘ pr₁))

\end{code}
