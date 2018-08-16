Martin Escardo, August 2018.

A structure identity principle for types, rather than categories as in
the HoTT Book.

This is related to work by Coquand and Danielsson (2013)

We give some examples at the end.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-Yoneda

module UF-GSIP where

\end{code}

For the moment we postulate the computation rule for equivalence
induction because I haven't proved it yet, but it is known to hold
(and we have the material needed to show this):

\begin{code}

postulate
 JEq-comp : ∀ {U} (ua : is-univalent U)
           {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇) (b : A X (≃-refl X))
        → JEq ua X A b X (≃-refl X) ≡ b
{-
JEq-comp ua X A b = γ
 where
  γ : transport (A X)
        (idtoeq-eqtoid ua X X (≃-refl X))
        (Jbased X (λ Y p → A Y (idtoeq X Y p)) b X (eqtoid ua X X (≃-refl X)))
    ≡ b
  γ = {!!}
-}

\end{code}

We consider the type 𝕊 of types X equipped with structure m : S X,
where S is a parameter:

\begin{code}

module gsip₀
        (U V : Universe)
        (ua : is-univalent U)
        (S : U ̇ → V ̇)
       where

 𝕊 : U ′ ⊔ V ̇
 𝕊 = Σ \(X : U ̇) → S X

\end{code}

The underlying set and structure are given by the first and second
projections:

\begin{code}

 ⟨_⟩ : 𝕊 → U ̇
 ⟨ X , m ⟩ = X

 structure : (A : 𝕊) → S ⟨ A ⟩
 structure (X , s) = s

\end{code}

 If S comes with suitable data, we can characterize equality in 𝕊 as
 equivalence of underlying sets with data. One possible set of data
 for S is the following:

\begin{code}

 module gsip₁
         (S-equiv : (A B : 𝕊) → (f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f → U ⊔ V ̇)
         (S-refl : (A : 𝕊) → S-equiv A A id (id-is-equiv ⟨ A ⟩))
         (one-structure : (X : U ̇) (m n : S X) → S-equiv (X , m) (X , n) id (id-is-equiv X) → m ≡ n)
         (S-transport : (A : 𝕊) (m : S ⟨ A ⟩) (t : S-equiv (⟨ A ⟩ , structure A) (⟨ A ⟩ , m) id (id-is-equiv ⟨ A ⟩))
                      → transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩))
                               (one-structure ⟨ A ⟩ (structure A) m t)
                               (S-refl A)
                      ≡ t)
        where


\end{code}

 We show that equality in 𝕊 is equivalent _≃ₛ_ defined as follows:

\begin{code}

  _≃ₛ_ : 𝕊 → 𝕊 → U ⊔ V ̇
  A ≃ₛ B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → Σ \(e : is-equiv f) → S-equiv A B f e

  ≃ₛ-refl : (A : 𝕊) → A ≃ₛ A
  ≃ₛ-refl A = id , id-is-equiv ⟨ A ⟩ , S-refl A

  idtoeqₛ : (A B : 𝕊) → A ≡ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

  private
    Ψ : (A : 𝕊) (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ′ ⊔ V ̇
    Ψ A Y (f , e) = (m : S Y) (t : S-equiv A (Y , m) f e) → A ≡ (Y , m)
    ψ : (A : 𝕊) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A m t = to-Σ-≡' (one-structure ⟨ A ⟩ (structure A) m t)

  eqtoidₛ : (A B : 𝕊) → A ≃ₛ B → A ≡ B
  eqtoidₛ A B (f , e , t) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) t

  idtoeq-eqtoidₛ : (A B : 𝕊) (ψ : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ψ) ≡ ψ
  idtoeq-eqtoidₛ A B (f , e , t) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) t
   where
    Φ : (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ⊔ V ̇
    Φ Y (f , e) = (m : S Y)
                  (t : S-equiv A (Y , m) f e)
                → idtoeqₛ A (Y , m) (eqtoidₛ A (Y , m) (f , e , t)) ≡ f , e , t
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ m t = γ
     where
      A' : 𝕊
      A' = ⟨ A ⟩ , m
      observation₀ : A ≡ A'
      observation₀ = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t
      observation₁ : S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      observation₁ = t
      refl' : A ≃ₛ A'
      refl' = id , id-is-equiv ⟨ A ⟩ , t
      observation₂ : eqtoidₛ A A' refl' ≡ JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t
      observation₂ = refl
      p : structure A ≡ m
      p = one-structure ⟨ A ⟩ (structure A) m t
      q : JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t ≡ to-Σ-≡' p
      q = ap (λ h → h m t) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A))
      r : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ idtoeqₛ A A' (to-Σ-≡' p)
      r = ap (idtoeqₛ A A') q
      s : structure A ≡ m → S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      s p = transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩)) p (S-refl A)
      u : s p ≡ t
      u = S-transport A m t
      v : id , id-is-equiv ⟨ A ⟩ , s p ≡ refl'
      v = to-Σ-≡' (to-Σ-≡' u)
      w : (p : structure A ≡ m) → idtoeqₛ A A' (to-Σ-≡' p) ≡ id , id-is-equiv ⟨ A ⟩ , s p
      w refl = refl
      x : idtoeqₛ A A' (to-Σ-≡' p) ≡ refl'
      x = w p ∙ v
      γ : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ refl'
      γ = r ∙ x

  uaₛ : (A B : 𝕊) → is-equiv (idtoeqₛ A B)
  uaₛ A = nat-retraction-is-equiv A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : 𝕊) (p : A ≡ B) →  eqtoidₛ A B (idtoeqₛ A B p) ≡ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (is-equiv-qinv (idtoeqₛ A B) (uaₛ A B)))

\end{code}

A magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of equality of magmas:

\begin{code}

module magma-experiment (U : Universe) (ua : is-univalent U) where

 open gsip₀ U U ua (λ X → X → X → X)
 open gsip₁ (λ A B f e → (λ x x' → f (structure A x x')) ≡ (λ x x' → structure B (f x) (f x')))
            (λ A → refl)
            (λ X m n t → t)
            (λ A m t → refl-left-neutral)

 fact : (A B : 𝕊) → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f × ((λ x x' → f (structure A x x')) ≡
                                                                       (λ x x' → structure B (f x) (f x')))
 fact A B = idtoeqₛ A B , uaₛ A B

 fact' : (X Y : U ̇) (m : X → X → X) (n : Y → Y → Y)
      → ((X , m) ≡ (Y , n))
      ≃ Σ \(f : X → Y) → is-equiv f × ((λ x x' → f (m x x')) ≡ (λ x x' → n (f x) (f x')))
 fact' X Y m n = fact (X , m) (Y , n)

\end{code}

A topology on a set X is a set of subsets satisfying suitable
axioms. A set of subsets is a map (X → Ω) → Ω. Dropping the assumption
that X is a set and the axioms for topologies, and generalizing Ω to
an arbitrary type R, we get proto-topological types.

\begin{code}

module proto-topology-experiment (U V : Universe) (ua : is-univalent U) (R : V ̇) where

 open gsip₀ U (U ⊔ V) ua (λ X → (X → R) → R)
 open gsip₁ (λ A B f e → (λ V → structure A (V ∘ f)) ≡ structure B )
            (λ A → refl)
            (λ X m n p → p)
            (λ A m t → refl-left-neutral)

 fact : (A B : 𝕊) → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f × ((λ V → structure A (λ x → V (f x))) ≡ structure B)
 fact A B = idtoeqₛ A B , uaₛ A B

 fact' : (X Y : U ̇) (τ : (X → R) → R) (σ : (Y → R) → R)
      → ((X , τ) ≡ (Y , σ)) ≃ Σ \(f : X → Y) → is-equiv f × ((λ V → τ (V ∘ f)) ≡ σ)
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

If we say that an equivalence f is a homeomorphism when a set is
σ-open precisely when its f-inverse image is τ-open, then the above
says that two proto-topological types are equal iff they are
homeomorphic.

Perhaps it is possible to derive the SIP for 1-categories from the
above SIP for types equipped with structure.
