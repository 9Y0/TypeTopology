Tom de Jong, early January 2022.

We define when a dcpo is (structurally) continuous/algebraic and prove the
nullary, unary and binary interpolation properties of the way-below relation in
a continuous dcpo.

We also show that in a continuous dcpo being locally small is equivalent to the
way-below relation having small truth values. Further, being (structurally)
continuous is preserved by taking continuous retracts.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.Continuity
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.IndCompletion pt fe 𝓥

\end{code}

We first define an untruncated, non-propositional, version of continuity for
dcpos, which we call structural continuity. The notion of a continuous dcpo will
then be given by truncating the type expressing its structural continuity.

The motivation for our definition of continuity is discussed in
ContinuityDiscussion.lagda.

We use record syntax to have descriptively named projections available without
having to add them as boilerplate.

\begin{code}

record structurally-continuous (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
 field
  index-of-approximating-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  approximating-family : (x : ⟨ 𝓓 ⟩)
                       → (index-of-approximating-family x) → ⟨ 𝓓 ⟩
  approximating-family-is-directed : (x : ⟨ 𝓓 ⟩)
                                   → is-Directed 𝓓 (approximating-family x)
  approximating-family-is-way-below : (x : ⟨ 𝓓 ⟩)
                                    → is-way-upperbound 𝓓 x
                                       (approximating-family x)
  approximating-family-∐-＝ : (x : ⟨ 𝓓 ⟩)
                           → ∐ 𝓓 (approximating-family-is-directed x) ＝ x

 approximating-family-∐-⊑ : (x : ⟨ 𝓓 ⟩)
                          → ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ x
 approximating-family-∐-⊑ x = ＝-to-⊑ 𝓓 (approximating-family-∐-＝ x)

 approximating-family-∐-⊒ : (x : ⟨ 𝓓 ⟩)
                          → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (approximating-family-is-directed x)
 approximating-family-∐-⊒ x = ＝-to-⊒ 𝓓 (approximating-family-∐-＝ x)

is-continuous-dcpo : DCPO {𝓤} {𝓣} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-continuous-dcpo 𝓓 = ∥ structurally-continuous 𝓓 ∥

being-continuous-dcpo-is-prop : (𝓓 : DCPO {𝓤} {𝓣})
                              → is-prop (is-continuous-dcpo 𝓓)
being-continuous-dcpo-is-prop 𝓓 = ∥∥-is-prop

\end{code}

Similarly, we define when a dcpo is (structurally) algebraic where the
approximating family is required to consist of compact elements.

\begin{code}

record structurally-algebraic (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
 field
  index-of-compact-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  compact-family : (x : ⟨ 𝓓 ⟩) → (index-of-compact-family x) → ⟨ 𝓓 ⟩
  compact-family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (compact-family x)
  compact-family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index-of-compact-family x)
                            → is-compact 𝓓 (compact-family x i)
  compact-family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (compact-family-is-directed x) ＝ x

 compact-family-is-upperbound : (x : ⟨ 𝓓 ⟩)
                              → is-upperbound (underlying-order 𝓓)
                                              x (compact-family x)
 compact-family-is-upperbound x i =
  compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
  ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
  x                                  ∎⟨ 𝓓 ⟩
   where
    ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
    ⦅2⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

is-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic-dcpo 𝓓 = ∥ structurally-algebraic 𝓓 ∥

structurally-continuous-if-structurally-algebraic :
   (𝓓 : DCPO {𝓤} {𝓣})
 → structurally-algebraic 𝓓 → structurally-continuous 𝓓
structurally-continuous-if-structurally-algebraic 𝓓 sa =
 record
  { index-of-approximating-family     = index-of-compact-family
  ; approximating-family              = compact-family
  ; approximating-family-is-directed  = compact-family-is-directed
  ; approximating-family-is-way-below = γ
  ; approximating-family-∐-＝          = compact-family-∐-＝
  }
  where
   open structurally-algebraic sa
   γ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (compact-family x)
   γ x i = ≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
                      (compact-family-is-upperbound x i)

is-continuous-dcpo-if-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                                     → is-algebraic-dcpo 𝓓
                                     → is-continuous-dcpo 𝓓
is-continuous-dcpo-if-algebraic-dcpo 𝓓 =
 ∥∥-functor (structurally-continuous-if-structurally-algebraic 𝓓)

\end{code}

We characterize the order in a structurally continuous dcpo using approximating
families.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 structurally-continuous-⊑-criterion :
    {x y : ⟨ 𝓓 ⟩}
  → ((i : index-of-approximating-family x) → approximating-family x i ⊑⟨ 𝓓 ⟩ y)
  → x ⊑⟨ 𝓓 ⟩ y
 structurally-continuous-⊑-criterion {x} {y} l =
  transport (λ - → - ⊑⟨ 𝓓 ⟩ y) (approximating-family-∐-＝ x) γ
   where
    γ : ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ y
    γ = ∐-is-lowerbound-of-upperbounds 𝓓 (approximating-family-is-directed x) y l

 structurally-continuous-⊑-criterion' :
    {x y : ⟨ 𝓓 ⟩}
  → ((i : index-of-approximating-family x) → approximating-family x i ≪⟨ 𝓓 ⟩ y)
  → x ⊑⟨ 𝓓 ⟩ y
 structurally-continuous-⊑-criterion' {x} {y} l =
  structurally-continuous-⊑-criterion (λ i → ≪-to-⊑ 𝓓 (l i))

 structurally-continuous-⊑-criterion'-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ⊑⟨ 𝓓 ⟩ y
  → ((i : index-of-approximating-family x) → approximating-family x i ≪⟨ 𝓓 ⟩ y)
 structurally-continuous-⊑-criterion'-converse {x} {y} l i =
  ≪-⊑-to-≪ 𝓓 (approximating-family-is-way-below x i) l

 structurally-continuous-⊑-criterion-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ⊑⟨ 𝓓 ⟩ y
  → ((i : index-of-approximating-family x) → approximating-family x i ⊑⟨ 𝓓 ⟩ y)
 structurally-continuous-⊑-criterion-converse {x} {y} l i =
  ≪-to-⊑ 𝓓 (structurally-continuous-⊑-criterion'-converse l i)

\end{code}

We also characterize the way-below relation in terms of the order and
approximating families.

\begin{code}

 structurally-continuous-≪-criterion :
    {x y : ⟨ 𝓓 ⟩}
  → (∃ i ꞉ index-of-approximating-family y , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
  → x ≪⟨ 𝓓 ⟩ y
 structurally-continuous-≪-criterion {x} {y} = ∥∥-rec (≪-is-prop-valued 𝓓) γ
  where
   γ : (Σ i ꞉ index-of-approximating-family y
            , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
     → x ≪⟨ 𝓓 ⟩ y
   γ (i , l) = ⊑-≪-to-≪ 𝓓 l (approximating-family-is-way-below y i)

 structurally-continuous-≪-criterion-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ≪⟨ 𝓓 ⟩ y
  → (∃ i ꞉ index-of-approximating-family y , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
 structurally-continuous-≪-criterion-converse {x} {y} wb =
  wb (index-of-approximating-family y) (approximating-family y)
     (approximating-family-is-directed y) (approximating-family-∐-⊒ y)

\end{code}

We set out to prove nullary, unary and binary interpolation for (structurally)
continuous dcpos.

\begin{code}

 ≪-nullary-interpolation-str : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation-str x =
  ∥∥-functor γ (inhabited-if-Directed 𝓓 (approximating-family x)
                                        (approximating-family-is-directed x))
   where
    γ : index-of-approximating-family x → Σ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
    γ i = (approximating-family x i , approximating-family-is-way-below x i)

\end{code}

Our proof of the unary interpolation property is inspired by Proposition 2.12 of
"Continuous categories and Exponentiable Toposes" by Peter Johnstone and André
Joyal. The idea is to approximate y by a family αᵢ, approximate each αᵢ by
another family βᵢⱼ, and finally to approximate y as the "sum" of the βᵢⱼs.

\begin{code}

 ≪-unary-interpolation-str : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                           → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation-str {x} {y} x-way-below-y = interpol
  where
   Iʸ : 𝓥 ̇
   Iʸ = index-of-approximating-family y
   αʸ : Iʸ → ⟨ 𝓓 ⟩
   αʸ = approximating-family y
   δʸ : is-Directed 𝓓 αʸ
   δʸ = approximating-family-is-directed y
   J : (i : Iʸ) → 𝓥 ̇
   J i = index-of-approximating-family (αʸ i)
   β : (i : Iʸ) → J i → ⟨ 𝓓 ⟩
   β i = approximating-family (αʸ i)
   δ : (i : Iʸ) → is-Directed 𝓓 (β i)
   δ i = approximating-family-is-directed (αʸ i)

   open Ind-completion 𝓓
   𝓑 : Iʸ → Ind
   𝓑 i = J i , β i , δ i
   𝓘 : Ind
   𝓘 = Ind-∐ 𝓑 (inhabited-if-Directed 𝓓 αʸ δʸ , σ)
    where
     σ : is-semidirected _≲_ 𝓑
     σ i₁ i₂ = ∥∥-functor r (semidirected-if-Directed 𝓓 αʸ δʸ i₁ i₂)
      where
       r : (Σ i ꞉ Iʸ , (αʸ i₁ ⊑⟨ 𝓓 ⟩ αʸ i) × (αʸ i₂ ⊑⟨ 𝓓 ⟩ αʸ i))
         → Σ i ꞉ Iʸ , (𝓑 i₁ ≲ 𝓑 i) × (𝓑 i₂ ≲ 𝓑 i)
       r (i , u , v) = i , l₁ , l₂
        where
         w = approximating-family-∐-⊒ (αʸ i)
         l₁ : 𝓑 i₁ ≲ 𝓑 i
         l₁ j = approximating-family-is-way-below (αʸ i₁) j (J i) (β i) (δ i)
                 (αʸ i₁     ⊑⟨ 𝓓 ⟩[ u ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)
         l₂ : 𝓑 i₂ ≲ 𝓑 i
         l₂ j = approximating-family-is-way-below (αʸ i₂) j (J i) (β i) (δ i)
                 (αʸ i₂     ⊑⟨ 𝓓 ⟩[ v ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)

   K : 𝓥 ̇
   K = pr₁ 𝓘
   γ : K → ⟨ 𝓓 ⟩
   γ = pr₁ (pr₂ 𝓘)
   γ-is-directed : is-Directed 𝓓 γ
   γ-is-directed = pr₂ (pr₂ 𝓘)

   y-below-∐-of-γ : y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
   y-below-∐-of-γ = structurally-continuous-⊑-criterion u
    where
     u : (i : Iʸ) → αʸ i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
     u i = structurally-continuous-⊑-criterion v
      where
       v : (j : J i) → β i j ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
       v j = ∐-is-upperbound 𝓓 γ-is-directed (i , j)

   x-below-γ : ∃ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k
   x-below-γ = x-way-below-y K γ γ-is-directed y-below-∐-of-γ

   interpol : ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
   interpol = ∥∥-functor r lemma
    where
     r : (Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                               × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                               × (αʸ i ≪⟨ 𝓓 ⟩ y))
       → Σ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
     r (i , j , u , v , w) = (αʸ i , ⊑-≪-to-≪ 𝓓 u v , w)
     lemma : ∥ Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                    × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                    × (αʸ i ≪⟨ 𝓓 ⟩ y) ∥
     lemma = ∥∥-functor s x-below-γ
      where
       s : (Σ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k)
         → Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                × (αʸ i ≪⟨ 𝓓 ⟩ y)
       s ((i , j) , l) = (i , j , l ,
                          approximating-family-is-way-below (αʸ i) j ,
                          approximating-family-is-way-below y i)

\end{code}

From the unary interpolation property, one quickly derives the binary version,
although the proof involves eliminating several propositional truncations. For
that reason, we use so-called do-notation (which is possible because ∥-∥ is a
monad) to shorten the proof below. If we write x ← t, then x : X and t : ∥ X ∥.

\begin{code}

 ≪-binary-interpolation-str : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                            → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                          × (y ≪⟨ 𝓓 ⟩ d)
                                          × (d ≪⟨ 𝓓 ⟩ z)
 ≪-binary-interpolation-str {x} {y} {z} x-way-below-z y-way-below-z = do
  let δ = approximating-family-is-directed z
  let l = approximating-family-∐-⊒ z
  (d₁ , x-way-below-d₁ , d₁-way-below-z) ← ≪-unary-interpolation-str
                                            x-way-below-z
  (d₂ , y-way-below-d₂ , d₂-way-below-z) ← ≪-unary-interpolation-str
                                            y-way-below-z

  (i₁ , d₁-below-zⁱ₁)                    ← d₁-way-below-z _ _ δ l
  (i₂ , d₂-below-zⁱ₂)                    ← d₂-way-below-z _ _ δ l

  (i , zⁱ₁-below-zⁱ , zⁱ₂-below-zⁱ)      ← semidirected-if-Directed 𝓓 _ δ i₁ i₂
  let α = approximating-family z
  let d₁-below-αⁱ = d₁   ⊑⟨ 𝓓 ⟩[ d₁-below-zⁱ₁ ]
                    α i₁ ⊑⟨ 𝓓 ⟩[ zⁱ₁-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  let d₂-below-αⁱ = d₂   ⊑⟨ 𝓓 ⟩[ d₂-below-zⁱ₂ ]
                    α i₂ ⊑⟨ 𝓓 ⟩[ zⁱ₂-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  ∣ approximating-family z i , ≪-⊑-to-≪ 𝓓 x-way-below-d₁ d₁-below-αⁱ
                             , ≪-⊑-to-≪ 𝓓 y-way-below-d₂ d₂-below-αⁱ
                             , approximating-family-is-way-below z i ∣

\end{code}

The interpolation properties for continuous dcpos now follow immediately.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (c : is-continuous-dcpo 𝓓)
       where

 ≪-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation x =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-nullary-interpolation-str 𝓓 C x) c

 ≪-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                       → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation x-way-below-y =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-unary-interpolation-str 𝓓 C x-way-below-y) c

 ≪-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                        → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                      × (y ≪⟨ 𝓓 ⟩ d)
                                      × (d ≪⟨ 𝓓 ⟩ z)
 ≪-binary-interpolation {x} {y} {z} u v =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-binary-interpolation-str 𝓓 C u v) c

\end{code}

We show that in a (structurally) continuous dcpo local smallness is logically
equivalent to the way-below relation having small values.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 ≪-is-small-valued-str : is-locally-small 𝓓
                       → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
 ≪-is-small-valued-str ls x y = (∃ i ꞉ I , x ⊑ₛ α i) , ψ
  where
   open is-locally-small ls
   I : 𝓥 ̇
   I = index-of-approximating-family y
   α : I → ⟨ 𝓓 ⟩
   α = approximating-family y
   ψ = (∃ i ꞉ I , x ⊑ₛ      α i) ≃⟨ ∃-cong pt (λ i → ⊑ₛ-≃-⊑) ⟩
       (∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩  α i) ≃⟨ e ⟩
       x ≪⟨ 𝓓 ⟩ y                ■
    where
     e = logically-equivalent-props-are-equivalent ∃-is-prop (≪-is-prop-valued 𝓓)
          (structurally-continuous-≪-criterion 𝓓 C)
          (structurally-continuous-≪-criterion-converse 𝓓 C)

 ≪-is-small-valued-str-converse : ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                                → is-locally-small 𝓓
 ≪-is-small-valued-str-converse ≪-is-small-valued =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
   where
    _≪ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
    x ≪ₛ y = pr₁ (≪-is-small-valued x y)
    ≪ₛ-≃-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y ≃ x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-≃-≪ {x} {y} = pr₂ (≪-is-small-valued x y)
    γ : (x y : ⟨ 𝓓 ⟩) → is-small (x ⊑⟨ 𝓓 ⟩ y)
    γ x y = (∀ (i : I) → α i ≪ₛ y) , ψ
     where
      I : 𝓥 ̇
      I = index-of-approximating-family x
      α : I → ⟨ 𝓓 ⟩
      α = approximating-family x
      ψ = (∀ (i : I) → α i ≪ₛ     y) ≃⟨ Π-cong fe fe (λ i → ≪ₛ-≃-≪) ⟩
          (∀ (i : I) → α i ≪⟨ 𝓓 ⟩ y) ≃⟨ e ⟩
          x ⊑⟨ 𝓓 ⟩ y                 ■
       where
        e = logically-equivalent-props-are-equivalent
             (Π-is-prop fe (λ i → ≪-is-prop-valued 𝓓)) (prop-valuedness 𝓓 x y)
             (structurally-continuous-⊑-criterion' 𝓓 C)
             (structurally-continuous-⊑-criterion'-converse 𝓓 C)

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
        (c : is-continuous-dcpo 𝓓)
       where

 open import UF.Size hiding (is-small ; is-locally-small)

 abstract -- for performance
  ≪-is-small-valued : is-locally-small 𝓓
                    → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
  ≪-is-small-valued ls x y = ∥∥-rec p (λ C → ≪-is-small-valued-str 𝓓 C ls x y) c
   where
    p : is-prop (is-small (x ≪⟨ 𝓓 ⟩ y))
    p = prop-being-small-is-prop (λ _ → pe) (λ _ _ → fe)
         (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)

  ≪-is-small-valued-converse : ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                             → is-locally-small 𝓓
  ≪-is-small-valued-converse ws =
   ∥∥-rec (being-locally-small-is-prop 𝓓 (λ _ → pe))
    (λ C → ≪-is-small-valued-str-converse 𝓓 C ws) c

\end{code}

Finally, we prove that (structural) continuity is preserved by continuous
retracts.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 structural-continuity-of-dcpo-preserved-by-continuous-retract :
    structurally-continuous 𝓔
  → structurally-continuous 𝓓
 structural-continuity-of-dcpo-preserved-by-continuous-retract C =
  record
   { index-of-approximating-family     = λ x → index-of-approximating-family
                                                (s x)
   ; approximating-family              = λ x → r ∘ approximating-family (s x)
   ; approximating-family-is-directed  = lemma₁
   ; approximating-family-is-way-below = lemma₂
   ; approximating-family-∐-＝          = lemma₃
   }
   where
    open structurally-continuous C
    α : (y : ⟨ 𝓔 ⟩) → index-of-approximating-family y → ⟨ 𝓔 ⟩
    α = approximating-family
    lemma₁ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (r ∘ α (s x))
    lemma₁ x = image-is-directed' 𝓔 𝓓 𝕣
                (approximating-family-is-directed (s x))
    lemma₂ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (r ∘ α (s x))
    lemma₂ x i = continuous-retraction-≪-criterion 𝓓 𝓔 ρ (α (s x) i) x
                  (approximating-family-is-way-below (s x) i)
    lemma₃ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (lemma₁ x) ＝ x
    lemma₃ x = ∐ 𝓓 (lemma₁ x) ＝⟨ ⦅1⦆ ⟩
               r (∐ 𝓔 δ)      ＝⟨ ⦅2⦆ ⟩
               r (s x)        ＝⟨ ⦅3⦆ ⟩
               x              ∎
     where
      δ : is-Directed 𝓔 (α (s x))
      δ = approximating-family-is-directed (s x)
      ⦅1⦆ = (continuous-∐-＝ 𝓔 𝓓 𝕣 δ) ⁻¹
      ⦅2⦆ = ap r (approximating-family-∐-＝ (s x))
      ⦅3⦆ = s-section-of-r x

 continuity-of-dcpo-preserved-by-continuous-retract : is-continuous-dcpo 𝓔
                                                    → is-continuous-dcpo 𝓓
 continuity-of-dcpo-preserved-by-continuous-retract =
  ∥∥-functor structural-continuity-of-dcpo-preserved-by-continuous-retract

\end{code}

If we assume propositional resizing, we can recover a continuity/algebraic
structure on 𝓓 from the respective properties.

\begin{code}

module _ where

 open import UF.Size hiding (is-locally-small; is-small)

 structurally-continuous-if-continuous : (psz : propositional-resizing (𝓥 ⁺ ⊔ 𝓣) 𝓥)
                                         (𝓓 : DCPO {𝓥} {𝓣})
                                       → is-continuous-dcpo 𝓓
                                       → structurally-continuous 𝓓
 structurally-continuous-if-continuous psz 𝓓 c =
  record
   { index-of-approximating-family = index
   ; approximating-family = family
   ; approximating-family-is-directed = family-is-directed
   ; approximating-family-is-way-below = family-is-way-below
   ; approximating-family-∐-＝ = family-∐-＝
   }
   where
    index : ⟨ 𝓓 ⟩ → 𝓥 ̇
    index x = Σ y ꞉ ⟨ 𝓓 ⟩ , resize psz (y ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓)

    make-index : {x : ⟨ 𝓓 ⟩} (y : ⟨ 𝓓 ⟩) → y ≪⟨ 𝓓 ⟩ x → index x
    make-index y p = y , (to-resize psz _ (≪-is-prop-valued 𝓓) p)

    family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
    family x = pr₁

    ≪-from-resize : {x y : ⟨ 𝓓 ⟩}
                   → resize psz (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)
                   → x ≪⟨ 𝓓 ⟩ y
    ≪-from-resize p = from-resize psz _ (≪-is-prop-valued 𝓓) p

    family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (family x)
    family-is-directed x = ∥∥-rec (being-directed-is-prop _ (family x)) γ c
     where
      γ : structurally-continuous 𝓓 → is-Directed 𝓓 (family x)
      γ sc = family-is-inhabited , family-is-semidirected
       where
        open structurally-continuous sc

        approximating-family-index-to-index : {x : ⟨ 𝓓 ⟩}
                                              (i : index-of-approximating-family x)
                                            → index x
        approximating-family-index-to-index {x} i =
         make-index (approximating-family x i)
          (approximating-family-is-way-below x i)

        family-is-inhabited : ∥ index x ∥
        family-is-inhabited =
         ∥∥-functor
          approximating-family-index-to-index
          (inhabited-if-Directed 𝓓 _ (approximating-family-is-directed x))

        family-is-semidirected : is-Semidirected 𝓓 (family x)
        family-is-semidirected (y₁ , y₁≪x) (y₂ , y₂≪x) =
         ∥∥-rec₂ ∃-is-prop f h1 h2
         where
           f : Σ i ꞉ index-of-approximating-family x , y₁ ⊑⟨ 𝓓 ⟩ approximating-family x i
             → Σ j ꞉ index-of-approximating-family x , y₂ ⊑⟨ 𝓓 ⟩ approximating-family x j
             → ∃ k ꞉ index x , y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                               y₂ ⊑⟨ 𝓓 ⟩ family x k
           f (i , y₁⊑αᵢ) (j , y₂⊑αⱼ) =
            ∥∥-functor g (semidirected-if-Directed 𝓓 _ (approximating-family-is-directed x) i j)
            where
             g : Σ k ꞉ index-of-approximating-family x ,
                  approximating-family x i ⊑⟨ 𝓓 ⟩ approximating-family x k ×
                  approximating-family x j ⊑⟨ 𝓓 ⟩ approximating-family x k
               → Σ k ꞉ index x ,
                  y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                  y₂ ⊑⟨ 𝓓 ⟩ family x k
             g (k , αᵢ⊑αₖ , αⱼ⊑αₖ) =
              approximating-family-index-to-index k ,
              transitivity 𝓓 _ _ _ y₁⊑αᵢ αᵢ⊑αₖ ,
              transitivity 𝓓 _ _ _ y₂⊑αⱼ αⱼ⊑αₖ

           h1 : ∃ i ꞉ index-of-approximating-family x , y₁ ⊑⟨ 𝓓 ⟩ approximating-family x i
           h1 = (≪-from-resize y₁≪x) _ _ (approximating-family-is-directed x)
                 (approximating-family-∐-⊒ x)

           h2 : ∃ i ꞉ index-of-approximating-family x , y₂ ⊑⟨ 𝓓 ⟩ approximating-family x i
           h2 = (≪-from-resize y₂≪x) _ _ (approximating-family-is-directed x)
                 (approximating-family-∐-⊒ x)

    family-is-way-below : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (family x)
    family-is-way-below x (y , y≪x) = ≪-from-resize y≪x

    family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
    family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ c
     where
      γ : structurally-continuous 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
      γ sc = antisymmetry 𝓓 _ _
              (∐-is-lowerbound-of-upperbounds 𝓓 _ _
                λ (y , y≪x) → ≪-to-⊑ 𝓓 (≪-from-resize y≪x))
              (x                                        ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               ∐ 𝓓 (family-is-directed x)               ∎⟨ 𝓓 ⟩)
       where
        open structurally-continuous sc

        ⦅1⦆ = approximating-family-∐-⊒ x

        ⦅2⦆ : ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
        ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 _ _
              λ i → ∐-is-upperbound 𝓓 (family-is-directed x)
                     (make-index
                      (approximating-family x i)
                      (approximating-family-is-way-below x i))

 structurally-algebraic-if-algebraic : (psz : propositional-resizing (𝓥 ⁺ ⊔ 𝓣) 𝓥)
                                       (𝓓 : DCPO {𝓥} {𝓣})
                                     → is-algebraic-dcpo 𝓓
                                     → structurally-algebraic 𝓓
 structurally-algebraic-if-algebraic psz 𝓓 a =
  record
   { index-of-compact-family = index
   ; compact-family = family
   ; compact-family-is-directed = family-is-directed
   ; compact-family-is-compact = family-is-compact
   ; compact-family-∐-＝ = family-∐-＝
   }
   where
    index : ⟨ 𝓓 ⟩ → 𝓥 ̇
    index x = Σ y ꞉ ⟨ 𝓓 ⟩ ,
               resize psz (is-compact 𝓓 y) (being-compact-is-prop 𝓓 y) ×
               resize psz (y ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓)

    make-index : {x : ⟨ 𝓓 ⟩} → (y : ⟨ 𝓓 ⟩) → is-compact 𝓓 y → y ≪⟨ 𝓓 ⟩ x → index x
    make-index y y≪y y≪x =
     y ,
     to-resize psz _ (being-compact-is-prop 𝓓 y) y≪y ,
     to-resize psz _ (≪-is-prop-valued 𝓓) y≪x

    family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
    family x = pr₁

    ≪-from-resize : {x y : ⟨ 𝓓 ⟩}
                   → resize psz (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)
                   → x ≪⟨ 𝓓 ⟩ y
    ≪-from-resize p = from-resize psz _ (≪-is-prop-valued 𝓓) p

    family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (family x)
    family-is-directed x = ∥∥-rec (being-directed-is-prop _ (family x)) γ a
     where
      γ : structurally-algebraic 𝓓 → is-Directed 𝓓 (family x)
      γ sa = family-is-inhabited , family-is-semidirected
       where
        open structurally-algebraic sa

        compact-family-index-to-index : {x : ⟨ 𝓓 ⟩}
                                        (i : index-of-compact-family x)
                                      → index x
        compact-family-index-to-index {x} i =
         make-index
          (compact-family x i)
          (compact-family-is-compact x i)
          (≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
           (compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
            ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
            x                                  ∎⟨ 𝓓 ⟩))
         where
          ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
          ⦅2⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

        family-is-inhabited : ∥ index x ∥
        family-is-inhabited =
         ∥∥-functor
          compact-family-index-to-index
          (inhabited-if-Directed 𝓓 _ (compact-family-is-directed x))

        family-is-semidirected : is-Semidirected 𝓓 (family x)
        family-is-semidirected (y₁ , y₁≪y₁ , y₁≪x) (y₂ , y₂≪y₂ , y₂≪x) =
         ∥∥-rec₂ ∃-is-prop f h1 h2
         where
          f : Σ i ꞉ index-of-compact-family x , y₁ ⊑⟨ 𝓓 ⟩ compact-family x i
            → Σ j ꞉ index-of-compact-family x , y₂ ⊑⟨ 𝓓 ⟩ compact-family x j
            → ∃ k ꞉ index x , y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                              y₂ ⊑⟨ 𝓓 ⟩ family x k
          f (i , y₁⊑αᵢ) (j , y₂⊑αⱼ) =
           ∥∥-functor g (semidirected-if-Directed 𝓓 _ (compact-family-is-directed x) i j)
           where
            g : Σ k ꞉ index-of-compact-family x ,
                 compact-family x i ⊑⟨ 𝓓 ⟩ compact-family x k ×
                 compact-family x j ⊑⟨ 𝓓 ⟩ compact-family x k
              → Σ k ꞉ index x ,
                 y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                 y₂ ⊑⟨ 𝓓 ⟩ family x k
            g (k , αᵢ⊑αₖ , αⱼ⊑αₖ) =
             compact-family-index-to-index k ,
             transitivity 𝓓 _ _ _ y₁⊑αᵢ αᵢ⊑αₖ ,
             transitivity 𝓓 _ _ _ y₂⊑αⱼ αⱼ⊑αₖ

          h1 : ∃ i ꞉ index-of-compact-family x , y₁ ⊑⟨ 𝓓 ⟩ compact-family x i
          h1 = ≪-from-resize y₁≪x _ _ _ (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

          h2 : ∃ j ꞉ index-of-compact-family x , y₂ ⊑⟨ 𝓓 ⟩ compact-family x j
          h2 = ≪-from-resize y₂≪x _ _ _ (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

    family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index x) → is-compact 𝓓 (family x i)
    family-is-compact x (y , y≪y , y≪x) = ≪-from-resize y≪y

    family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
    family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ a
     where
      γ : structurally-algebraic 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
      γ sa = antisymmetry 𝓓 _ _
              (∐-is-lowerbound-of-upperbounds 𝓓 _ _
                λ (y , y≪y , y≪x) → ≪-to-⊑ 𝓓 (≪-from-resize y≪x))
              (x                                  ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               ∐ 𝓓 (family-is-directed x)         ∎⟨ 𝓓 ⟩)
       where
        open structurally-algebraic sa

        ⦅1⦆ = ＝-to-⊒ 𝓓 (compact-family-∐-＝ x)

        ⦅2⦆ : ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
        ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 _ _ g
         where
          g : (i : index-of-compact-family x)
            → compact-family x i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
          g i = ∐-is-upperbound 𝓓 (family-is-directed x)
                 (make-index (compact-family x i) (compact-family-is-compact x i) αᵢ≪x)
           where
            αᵢ≪x : compact-family x i ≪⟨ 𝓓 ⟩ x
            αᵢ≪x = ≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
                    (compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅3⦆ ]
                     ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅4⦆ ]
                     x                                  ∎⟨ 𝓓 ⟩)
             where
              ⦅3⦆ = ∐-is-upperbound 𝓓 _ _
              ⦅4⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

\end{code}
