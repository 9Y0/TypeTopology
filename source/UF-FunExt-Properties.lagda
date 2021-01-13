Martin Escardo, 19th May 2018, 13th January 2021.

Properties of function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-FunExt-Properties where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts
open import UF-EquivalenceExamples

open import UF-FunExt

open import MGS-TypeTopology-Interface

import MGS-Equivalences
import MGS-FunExt-from-Univalence
import MGS-Universe-Lifting

\end{code}

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version.

\begin{code}

naive-funext-gives-funext' : naive-funext 𝓤 (𝓤 ⊔ 𝓥) → naive-funext 𝓤 𝓤 → funext 𝓤 𝓥
naive-funext-gives-funext' {𝓤} {𝓥} nfe nfe' = funext-via-singletons γ
 where
  γ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
    → ((x : X) → is-singleton (A x))
    → is-singleton (Π A)
  γ X A φ = δ
   where
    f : Σ A → X
    f = pr₁

    f-is-equiv : is-equiv f
    f-is-equiv = pr₁-equivalence X A φ

    g : (X → Σ A) → (X → X)
    g h = f ∘ h

    g-is-equiv : is-equiv g
    g-is-equiv = equiv-post nfe nfe' f f-is-equiv

    e : ∃! h ꞉ (X → Σ A) , f ∘ h ≡ id
    e = equivs-are-vv-equivs g g-is-equiv id

    r : (Σ h ꞉ (X → Σ A) , f ∘ h ≡ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))

    s : Π A → (Σ h ꞉ (X → Σ A) , f ∘ h ≡ id)
    s φ = (λ x → x , φ x) , refl

    rs : ∀ φ → r (s φ) ≡ φ
    rs φ = refl

    δ : is-singleton (Π A)
    δ = retract-of-singleton (r , s , rs) e

naive-funext-gives-funext : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

naive-funext-gives-funext₀ : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤₀
naive-funext-gives-funext₀ fe = naive-funext-gives-funext' fe fe

\end{code}

Interface to code from my MGS 2019 lecture notes:

\begin{code}

lower-DN-funext : ∀ 𝓦 𝓣 → DN-funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → DN-funext 𝓤 𝓥
lower-DN-funext {𝓤} {𝓥} 𝓦 𝓣 fe {X} {A} {f} {g} = MGS-Universe-Lifting.lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe

DN-funext-gives-funext : {𝓤 𝓥 : Universe} → DN-funext 𝓤 𝓥 → funext 𝓤 𝓥
DN-funext-gives-funext dnfe {X} {A} f g = γ
 where
  h : f ≡ g → f ∼ g
  h = MGS-FunExt-from-Univalence.happly f g

  a : is-equiv h
  a = MGS-equivs-are-equivs h (MGS-FunExt-from-Univalence.dfunext-gives-hfunext dnfe f g)

  b : is-equiv (happly' f g)
  b = equiv-closed-under-∼ h (happly' f g) a (happly'-is-MGS-happly f g)

  c :  MGS-Equivalences.is-equiv (happly' f g)
  c = equivs-are-MGS-equivs (happly' f g) b

  γ : is-equiv (happly' f g)
  γ = MGS-equivs-are-equivs (happly' f g) c

lower-funext : ∀ 𝓦 𝓣 → funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → funext 𝓤 𝓥
lower-funext {𝓤} {𝓥} 𝓦 𝓣 fe = DN-funext-gives-funext (lower-DN-funext 𝓦 𝓣 (dfunext fe))

\end{code}
