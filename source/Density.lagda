Martin Escardo 2011

A function is dense if the complement of its image is empty. Maybe
¬¬-surjective would be a better terminology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Density where

open import SpartanMLTT

open import UF-Equiv
open import UF-Retracts
open import UF-Embeddings

is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-dense f = is-empty (Σ y ꞉ codomain f , ¬ fiber f y)

id-is-dense : {X : 𝓤 ̇ } → is-dense (id {𝓤} {X})
id-is-dense (y , n) = n (y , refl)

comp-is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                {f : X → Y} {g : Y → Z}
              → is-dense f
              → is-dense g
              → is-dense (g ∘ f)
comp-is-dense {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} e d = h
 where
  h : ¬ (Σ z ꞉ Z , ¬ fiber (g ∘ f) z)
  h (z , n) = d (z , k)
   where
    k : ¬ fiber g z
    k (y , refl) = e (y , l)
     where
      l : ¬ fiber f y
      l (x , refl) = n (x , refl)


_↪ᵈ_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ᵈ Y = Σ f ꞉ (X → Y) , is-embedding f × is-dense f

module _ {𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } where

 retraction-is-dense : (r : X → Y) → has-section r → is-dense r
 retraction-is-dense r (s , rs) (y , n) = n (s y , rs y)

 equivs-are-dense : (f : X → Y) → is-equiv f → is-dense f
 equivs-are-dense f e = retraction-is-dense f (equivs-have-sections f e)

 equiv-dense-embedding : X ≃ Y → X ↪ᵈ Y
 equiv-dense-embedding e = ⌜ e ⌝ ,
                           equivs-are-embeddings ⌜ e ⌝ (⌜⌝-is-equiv e),
                           equivs-are-dense      ⌜ e ⌝ (⌜⌝-is-equiv e)

 detofun : (X ↪ᵈ Y) → X → Y
 detofun = pr₁

 is-embedding-detofun : (e : X ↪ᵈ Y) → is-embedding (detofun e)
 is-embedding-detofun e = pr₁ (pr₂ e)

 is-dense-detofun : (e : X ↪ᵈ Y) → is-dense (detofun e)
 is-dense-detofun e = pr₂ (pr₂ e)


\end{code}
