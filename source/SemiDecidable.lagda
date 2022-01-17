Tom de Jong, October--November 2021.

Refactored: January 2022.

We investigate constructive taboos surrounding semidecidability.

In particular, we try to investigate what form of countable choice, if any, is
necessary for the semidecidable propositions to be closed under countable joins.

Before we do that, we relate Bishop's Limited Principle of Omniscience (LPO),
Markov's Principle (MP) and strong Brouwer-Kripke-Scheme (BKS⁺) to properties of
the type of semidecidable propositions.

(See Appendix II of CantorSchroederBernstein.lagda for more BKS⁺.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- TODO: Clean this up

open import SpartanMLTT
open import UF-PropTrunc
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection

open import DecidableAndDetachable
open import DiscreteAndSeparated
open import Two-Properties
open import UF-Miscelanea

open import UF-Powerset
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt

open import UF-UniverseEmbedding

open import BinaryNaturals hiding (_+_)

open import NaturalsOrder
open import OrderNotation
open import Fin-Properties

open import CompactTypes

\end{code}

Part I: Basic definitions and properties of semidecidablity (structure).

\begin{code}

module SemiDecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
        (pt  : propositional-truncations-exist)
       where

fe' : FunExt
fe' 𝓤 𝓥 = fe

open PropositionalTruncation pt
open ImageAndSurjection pt

semidecidability-structure : (X : 𝓤 ̇  ) → 𝓤 ̇
semidecidability-structure X = Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

semidecidability-structure' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
semidecidability-structure' 𝓣 X = Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A
                                                  × (X ≃ (∃ n ꞉ ℕ , n ∈ A))

is-semidecidable : (X : 𝓤 ̇  ) → 𝓤 ̇
is-semidecidable X = ∥ semidecidability-structure X ∥

is-semidecidable' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
is-semidecidable' 𝓣 X = ∥ semidecidability-structure' 𝓣 X ∥

\end{code}

The difference between property and structure will be important in our
discussions regarding countable choice, as we will see later.

We proceed by showing that the primed versions are equivalent to the unprimed
versions above.

\begin{code}

semidecidability-structure-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                             → semidecidability-structure X
                             ≃ semidecidability-structure' 𝓣 X
semidecidability-structure-≃ {𝓤} {𝓣} {X} =
 (Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))                           ≃⟨ I   ⟩
 (Σ 𝔸 ꞉ (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A)
                          , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ 𝔸 n ≡ ₁))           ≃⟨ II  ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , Σ δ ꞉ is-decidable-subset A
                         , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ (A , δ) n ≡ ₁))      ≃⟨ III ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A × (X ≃ (∃ n ꞉ ℕ , n ∈ A))) ■
  where
   χ : (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A) ≃ (ℕ → 𝟚)
   χ = ≃-sym (𝟚-classifies-decidable-subsets fe fe pe)
   I   = ≃-sym (Σ-change-of-variable (λ α → X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))
          ⌜ χ ⌝ (⌜⌝-is-equiv χ))
   II  = Σ-assoc
   III = Σ-cong (λ A → Σ-cong
                (λ δ → ≃-cong-right fe' (∥∥-cong pt (Σ-cong (λ n → κ A δ n)))))
    where
     κ : (A : ℕ → Ω 𝓣) (δ : is-decidable-subset A) (n : ℕ )
       → (⌜ χ ⌝ (A , δ) n ≡ ₁) ≃ (A n holds)
     κ A δ n = logically-equivalent-props-are-equivalent
                    𝟚-is-set (holds-is-prop (A n))
                    (lr-implication (pr₂ lemma)) (rl-implication (pr₂ lemma))
      where
       lemma : ((⌜ χ ⌝ (A , δ) n ≡ ₀) ⇔ ¬ (n ∈ A))
             × ((⌜ χ ⌝ (A , δ) n ≡ ₁) ⇔   (n ∈ A))
       lemma = 𝟚-classifies-decidable-subsets-values fe fe pe A δ n

is-semidecidable-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                   → is-semidecidable X ≃ is-semidecidable' 𝓣 X
is-semidecidable-≃ = ∥∥-cong pt (semidecidability-structure-≃)

\end{code}

We proceed by proving some basic lemmas about semidecidability (structure).

\begin{code}

prop-if-semidecidability-structure : {X : 𝓤 ̇  }
                                   → semidecidability-structure X → is-prop X
prop-if-semidecidability-structure σ = equiv-to-prop (pr₂ σ) ∥∥-is-prop

prop-if-semidecidable : {X : 𝓤 ̇  } → is-semidecidable X → is-prop X
prop-if-semidecidable = ∥∥-rec (being-prop-is-prop fe)
                               prop-if-semidecidability-structure

being-semidecidable-is-prop : {X : 𝓤 ̇  } → is-prop (is-semidecidable X)
being-semidecidable-is-prop = ∥∥-is-prop

semidecidability-structure-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                                → X ≃ Y
                                → semidecidability-structure X
                                → semidecidability-structure Y
semidecidability-structure-cong {𝓤} {𝓥} f (ϕ , e) = (ϕ , (≃-sym f ● e))

is-semidecidable-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                      → X ≃ Y
                      → is-semidecidable X
                      → is-semidecidable Y
is-semidecidable-cong = ∥∥-functor ∘ semidecidability-structure-cong

\end{code}

The types 𝟘 and 𝟙 are semidecidable and hence, so are all singletons, empty
types and all decidable propositions.

\begin{code}

𝟘-has-semidecidability-structure' : semidecidability-structure (𝟘 {𝓤₀})
𝟘-has-semidecidability-structure' = ϕ , e
 where
  ϕ : ℕ → 𝟚
  ϕ _ = ₀
  ϕ-is-not-₁-anywhere : ¬ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  ϕ-is-not-₁-anywhere = forall₀-implies-not-exists₁ pt ϕ (λ _ → refl)
  e : 𝟘 ≃ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  e = ≃-sym (lr-implication negations-are-equiv-to-𝟘 ϕ-is-not-₁-anywhere)

𝟘-has-semidecidability-structure : semidecidability-structure (𝟘 {𝓤})
𝟘-has-semidecidability-structure {𝓤} =
 semidecidability-structure-cong γ 𝟘-has-semidecidability-structure'
  where
   γ : 𝟘 {𝓤₀} ≃ 𝟘 {𝓤}
   γ = qinveq 𝟘-elim (𝟘-elim , 𝟘-induction , 𝟘-induction)

𝟘-is-semidecidable : is-semidecidable (𝟘 {𝓤})
𝟘-is-semidecidable = ∣ 𝟘-has-semidecidability-structure ∣

empty-types-have-semidecidability-structure : {X : 𝓤 ̇  } → is-empty X
                                            → semidecidability-structure X
empty-types-have-semidecidability-structure e =
 semidecidability-structure-cong
  (≃-sym (lr-implication negations-are-equiv-to-𝟘 e))
  𝟘-has-semidecidability-structure

empty-types-are-semidecidable : {X : 𝓤 ̇  } → is-empty X → is-semidecidable X
empty-types-are-semidecidable e =
 ∣ empty-types-have-semidecidability-structure e ∣

𝟙-has-semidecidability-structure : semidecidability-structure (𝟙 {𝓤})
𝟙-has-semidecidability-structure = ϕ , e
 where
  ϕ : ℕ → 𝟚
  ϕ _ = ₁
  w : ∃ n ꞉ ℕ , ϕ n ≡ ₁
  w = ∣ 0 , refl ∣
  e : 𝟙 ≃ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  e = ≃-sym (lr-implication singletons-are-equiv-to-𝟙
              (w , (∥∥-is-prop w)))

𝟙-is-semidecidable : is-semidecidable (𝟙 {𝓤})
𝟙-is-semidecidable = ∣ 𝟙-has-semidecidability-structure ∣

singletons-have-semidecidability-structure : {X : 𝓤 ̇  } → is-singleton X
                                           → semidecidability-structure X
singletons-have-semidecidability-structure {𝓤} i =
 semidecidability-structure-cong
  (≃-sym (lr-implication singletons-are-equiv-to-𝟙 i))
  (𝟙-has-semidecidability-structure {𝓤})

singletons-are-semidecidable : {X : 𝓤 ̇  } → is-singleton X → is-semidecidable X
singletons-are-semidecidable i = ∣ singletons-have-semidecidability-structure i ∣

semidecidable-if-decidable-prop : {X : 𝓤 ̇  }
                                → is-prop X
                                → decidable X → is-semidecidable X
semidecidable-if-decidable-prop i (inl  x) = singletons-are-semidecidable (x , i x)
semidecidable-if-decidable-prop i (inr nx) = empty-types-are-semidecidable nx

\end{code}

If X and its negation ¬ X are semidecidable propositions, then so decidability
of X becomes semidecidable.

\begin{code}

decidability-is-semidecidable : (X : 𝓤 ̇  )
                              → is-semidecidable X
                              → is-semidecidable (¬ X)
                              → is-semidecidable (decidable X)
decidability-is-semidecidable X σ τ = ∥∥-rec being-semidecidable-is-prop ψ τ
 where
  ψ : semidecidability-structure (¬ X) → is-semidecidable (decidable X)
  ψ (β , g) = ∥∥-functor ϕ σ
   where
    ϕ : semidecidability-structure X → semidecidability-structure (decidable X)
    ϕ (α , f) = γ , h
     where
      γ : ℕ → 𝟚
      γ n = max𝟚 (α n) (β n)
      X-is-prop : is-prop X
      X-is-prop = prop-if-semidecidable σ
      dec-of-X-is-prop : is-prop (decidable X)
      dec-of-X-is-prop = decidability-of-prop-is-prop fe X-is-prop
      h : decidable X ≃ (∃ n ꞉ ℕ , γ n ≡ ₁)
      h = logically-equivalent-props-are-equivalent
           dec-of-X-is-prop ∥∥-is-prop u v
       where
        u : decidable X → ∃ n ꞉ ℕ , γ n ≡ ₁
        u (inl  x) = ∥∥-functor
                      (λ (n , b) → n , max𝟚-lemma-converse (α n) (β n) (inl b))
                      (⌜ f ⌝ x)
        u (inr nx) = ∥∥-functor
                      (λ (n , b) → n , max𝟚-lemma-converse (α n) (β n) (inr b))
                      (⌜ g ⌝ nx)
        v : ∃ n ꞉ ℕ , γ n ≡ ₁ → decidable X
        v = ∥∥-rec dec-of-X-is-prop ν
         where
          ν : (Σ n ꞉ ℕ , γ n ≡ ₁) → decidable X
          ν (n , p) = cases (λ a → inl (⌜ f ⌝⁻¹ ∣ n , a ∣))
                            (λ b → inr (⌜ g ⌝⁻¹ ∣ n , b ∣))
                            (max𝟚-lemma (α n) (β n) p)

\end{code}

Before ... TODO: Write more

\begin{code}

open import UF-Embeddings

open import CanonicalMapNotation

Ωˢᵈ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ωˢᵈ 𝓤 = Σ X ꞉ 𝓤 ̇  , is-semidecidable X

Ωˢᵈ-to-Ω : Ωˢᵈ 𝓤 → Ω 𝓤
Ωˢᵈ-to-Ω (X , σ) = (X , prop-if-semidecidable σ)

instance
 canonical-map-Ωˢᵈ-to-Ω : Canonical-Map (Ωˢᵈ 𝓤) (Ω 𝓤)
 ι {{canonical-map-Ωˢᵈ-to-Ω}} = Ωˢᵈ-to-Ω

Ωˢᵈ-to-Ω-left-cancellable : left-cancellable (canonical-map (Ωˢᵈ 𝓤) (Ω 𝓤))
Ωˢᵈ-to-Ω-left-cancellable {𝓤} {(X , σ)} {(Y , τ)} e =
 to-subtype-≡ (λ _ → being-semidecidable-is-prop) (ap pr₁ e)

Ωˢᵈ-to-Ω-is-embedding : is-embedding (canonical-map (Ωˢᵈ 𝓤) (Ω 𝓤))
Ωˢᵈ-to-Ω-is-embedding = lc-maps-into-sets-are-embeddings ι
                         Ωˢᵈ-to-Ω-left-cancellable (Ω-is-set fe pe)

Ωˢᵈ-is-set : {𝓤 : Universe} → is-set (Ωˢᵈ 𝓤)
Ωˢᵈ-is-set = subtypes-of-sets-are-sets ι Ωˢᵈ-to-Ω-left-cancellable
              (Ω-is-set fe pe)

-- TODO: Write comment

Ωᵈᵉᶜ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ωᵈᵉᶜ 𝓤 = Σ P ꞉ Ω 𝓤 , decidable (P holds)

Ωᵈᵉᶜ-to-Ωˢᵈ : Ωᵈᵉᶜ 𝓤 → Ωˢᵈ 𝓤
Ωᵈᵉᶜ-to-Ωˢᵈ ((P , i) , d) = (P , semidecidable-if-decidable-prop i d)

instance
 canonical-map-Ωᵈᵉᶜ-to-Ωˢᵈ : Canonical-Map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤)
 ι {{canonical-map-Ωᵈᵉᶜ-to-Ωˢᵈ}} = Ωᵈᵉᶜ-to-Ωˢᵈ

Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable : left-cancellable (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable {𝓤} {(X , _)} {(Y , _)} e =
 to-subtype-≡ (λ (P , i) → decidability-of-prop-is-prop fe i)
              (Ω-extensionality fe pe
               (idtofun (X holds) (Y holds) (ap pr₁ e))
               (idtofun (Y holds) (X holds) (ap pr₁ (e ⁻¹))))

Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding : is-embedding (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding = lc-maps-into-sets-are-embeddings ι
                            Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable
                            Ωˢᵈ-is-set

-- TODO: Write comment
𝟚-to-Ωˢᵈ : 𝟚 → Ωˢᵈ 𝓤
𝟚-to-Ωˢᵈ = Ωᵈᵉᶜ-to-Ωˢᵈ ∘ ⌜ 𝟚-is-the-type-of-decidable-propositions fe pe ⌝

instance
 canonical-map-𝟚-to-Ωˢᵈ : Canonical-Map 𝟚 (Ωˢᵈ 𝓤)
 ι {{canonical-map-𝟚-to-Ωˢᵈ}} = 𝟚-to-Ωˢᵈ

-- 𝟚-to-Ωˢᵈ-left-cancellable : left-cancellable (canonical-map 𝟚 (Ωˢᵈ 𝓤))
-- 𝟚-to-Ωˢᵈ-left-cancellable =

𝟚-to-Ωˢᵈ-is-embedding : is-embedding (canonical-map 𝟚 (Ωˢᵈ 𝓤))
𝟚-to-Ωˢᵈ-is-embedding {𝓤} =
 ∘-is-embedding (equivs-are-embeddings ⌜ χ ⌝ (⌜⌝-is-equiv χ))
                Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding
  where
   χ : 𝟚 ≃ Ωᵈᵉᶜ 𝓤
   χ = 𝟚-is-the-type-of-decidable-propositions fe pe

\end{code}

Part II(a): LPO and semidecidability

\begin{code}

LPO : 𝓤₀ ̇
LPO = (α : ℕ → 𝟚) → decidable (∃ n ꞉ ℕ , α n ≡ ₁)

LPO-is-prop : is-prop LPO
LPO-is-prop = Π-is-prop fe (λ α → decidability-of-prop-is-prop fe ∥∥-is-prop)

LPO' : (𝓤 : Universe) → 𝓤 ⁺ ̇
LPO' 𝓤 = (X : 𝓤 ̇  ) → is-semidecidable X → decidable X

LPO'-is-prop : {𝓤 : Universe} → is-prop (LPO' 𝓤)
LPO'-is-prop = Π₂-is-prop fe (λ X σ → decidability-of-prop-is-prop fe
                                       (prop-if-semidecidable σ))

\end{code}

LPO is a more traditional way of formulating LPO, but LPO' is perhaps
conceptually clearer and is the formulation that is most convenient for us
here. The two formulations are equivalent as proved below.

\begin{code}

LPO-equivalence : LPO ≃ LPO' 𝓤
LPO-equivalence {𝓤} = logically-equivalent-props-are-equivalent
                       LPO-is-prop LPO'-is-prop f g
 where
  f : LPO → LPO' 𝓤
  f lpo X σ = ∥∥-rec (decidability-of-prop-is-prop fe
                       (prop-if-semidecidable σ)) γ σ
   where
    γ : semidecidability-structure X → decidable X
    γ (α , e) = decidable-cong (≃-sym e) (lpo α)
  g : LPO' 𝓤 → LPO
  g τ α = decidable-cong (Lift-≃ 𝓤 X) (τ X' σ')
   where
    X : 𝓤₀ ̇
    X = ∃ n ꞉ ℕ , α n ≡ ₁
    X' : 𝓤 ̇
    X' = Lift 𝓤 X
    σ' : is-semidecidable X'
    σ' = is-semidecidable-cong (≃-sym (Lift-≃ 𝓤 X)) ∣ α , ≃-refl X ∣

\end{code}

By the above equivalence it follows that having LPO' in any universe is
equivalent to having LPO' in any other universe.

\begin{code}

LPO-across-universes : {𝓤 𝓥 : Universe} → LPO' 𝓤 ≃ LPO' 𝓥
LPO-across-universes {𝓤} {𝓥} = LPO' 𝓤  ≃⟨ ≃-sym LPO-equivalence ⟩
                                LPO    ≃⟨ LPO-equivalence       ⟩
                                LPO' 𝓥 ■

\end{code}

\begin{code}

LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ : {𝓤 : Universe}
                             → LPO' 𝓤 ≃ is-equiv (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ {𝓤} = logically-equivalent-props-are-equivalent
                                    LPO'-is-prop
                                    (being-equiv-is-prop (λ _ _ → fe) ι)
                                    ⦅⇒⦆ ⦅⇐⦆
   where
    ⦅⇒⦆ : LPO' 𝓤 → is-equiv ι
    ⦅⇒⦆ lpo = surjective-embeddings-are-equivs ι Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding
              (λ (X , σ) → ∣ ((X , prop-if-semidecidable σ) , lpo X σ)
                           , to-subtype-≡ (λ _ → being-semidecidable-is-prop)
                              refl ∣)
    ⦅⇐⦆ : is-equiv ι → LPO' 𝓤
    ⦅⇐⦆ ι-is-equiv X σ = transport decidable e Y-is-dec
     where
      β : Ωˢᵈ 𝓤 → Ωᵈᵉᶜ 𝓤
      β = inverse ι ι-is-equiv
      Y : 𝓤 ̇
      Y = pr₁ (β (X , σ)) holds
      Y-is-dec : decidable Y
      Y-is-dec = pr₂ (β (X , σ))
      e : Y ≡ X
      e = ap pr₁ (inverses-are-sections ι ι-is-equiv (X , σ))

LPO-in-terms-of-𝟚-and-Ωˢᵈ : {𝓤 : Universe}
                          → LPO ≃ is-equiv (canonical-map 𝟚 (Ωˢᵈ 𝓤))
LPO-in-terms-of-𝟚-and-Ωˢᵈ {𝓤} = logically-equivalent-props-are-equivalent
                                 LPO-is-prop (being-equiv-is-prop (λ _ _ → fe) ι)
                                 ⦅⇒⦆ ⦅⇐⦆
 where
  χ : 𝟚 ≃ Ωᵈᵉᶜ 𝓤
  χ = 𝟚-is-the-type-of-decidable-propositions fe pe
  ⦅⇒⦆ : LPO → is-equiv ι
  ⦅⇒⦆ lpo = ∘-is-equiv (⌜⌝-is-equiv χ)
            (⌜ LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ ⌝ (⌜ LPO-equivalence ⌝ lpo))
  ⦅⇐⦆ : is-equiv ι → LPO
  ⦅⇐⦆ i = ⌜ LPO-equivalence ⌝⁻¹
          (⌜ LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ ⌝⁻¹
            (≃-2-out-of-3-right (⌜⌝-is-equiv χ) i))

\end{code}

Part II(b):

\begin{code}

Semidecidable-Closed-Under-Negations : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidable-Closed-Under-Negations 𝓤 = (X : 𝓤 ̇  )
                                       → is-semidecidable X
                                       → is-semidecidable (¬ X)

semidecidable-negations-from-LPO : LPO' 𝓤
                                 → Semidecidable-Closed-Under-Negations 𝓤
semidecidable-negations-from-LPO lpo X σ =
 semidecidable-if-decidable-prop (negations-are-props fe)
  (¬-preserves-decidability (lpo X σ))

\end{code}



\begin{code}

\end{code}

Part II(d):

\begin{code}

\end{code}

Part III: ...

\begin{code}

-- TODO: Make a version with ∃ n ꞉ ℕ , ∃ m ꞉ ℕ instead?
semidecidability-pairing-lemma : {X : 𝓤 ̇  }
  → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
  ≃ semidecidability-structure X
semidecidability-pairing-lemma {𝓤} {X} =
 (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))            ≃⟨ I   ⟩
 (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))        ≃⟨ II  ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , ⌜ e₂ ⌝ ϕ (n , m) ≡ ₁)) ≃⟨ III ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ k ꞉ ℕ           , ϕ k ≡ ₁))              ■
 where
  e₁ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
  e₁ = curry-uncurry fe'
  e₂ : (ℕ → 𝟚) ≃ (ℕ × ℕ → 𝟚)
  e₂ = →cong'' fe fe (≃-sym pairing)
  I  = ≃-sym (Σ-change-of-variable (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
                                   ⌜ e₁ ⌝ (⌜⌝-is-equiv e₁))
  II = ≃-sym (Σ-change-of-variable
               (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
               ⌜ e₂ ⌝ (⌜⌝-is-equiv e₂))
  III = Σ-cong (λ ϕ → ≃-cong-right fe' (∥∥-cong pt (lemma ϕ)))
   where
    ρ : ℕ × ℕ ≃ ℕ
    ρ = pairing
    σ : (ℕ → 𝟚) → (ℕ × ℕ → 𝟚)
    σ = ⌜ e₂ ⌝
    lemma : (ϕ : ℕ → 𝟚)
          → (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m) ≡ ₁)
          ≃ (Σ k ꞉ ℕ , ϕ k ≡ ₁)
    lemma ϕ = (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m) ≡ ₁)           ≃⟨ ≃-sym Σ-assoc ⟩
              (Σ p ꞉ ℕ × ℕ       , σ ϕ p ≡ ₁)                 ≃⟨ ⦅i⦆           ⟩
              (Σ k ꞉ ℕ           , σ ϕ (⌜ ρ ⌝⁻¹ k) ≡ ₁)       ≃⟨ ≃-refl _      ⟩
              (Σ k ꞉ ℕ           , ϕ (⌜ ρ ⌝ (⌜ ρ ⌝⁻¹ k)) ≡ ₁) ≃⟨ ⦅ii⦆          ⟩
              (Σ k ꞉ ℕ           , ϕ k ≡ ₁)                   ■
     where
      ⦅i⦆  = ≃-sym (Σ-change-of-variable (λ p → σ ϕ p ≡ ₁) ⌜ ρ ⌝⁻¹ (⌜⌝⁻¹-is-equiv ρ))
      ⦅ii⦆ = Σ-cong (λ k → ≡-cong-l _ _ (ap ϕ (≃-sym-is-rinv ρ k)))

∃-has-semidecidability-structure : (X : ℕ → 𝓤 ̇  )
                                 → (Π n ꞉ ℕ , semidecidability-structure (X n))
                                 → semidecidability-structure (∃ X)
∃-has-semidecidability-structure X σ = ⌜ semidecidability-pairing-lemma ⌝ γ
 where
  γ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , ∃ X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁)
  γ = Ψ , e
   where
    lemma : (Π n ꞉ ℕ , semidecidability-structure (X n))
          → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , Π n ꞉ ℕ , X n ≃ (∃ m ꞉ ℕ , Ψ n m ≡ ₁))
    lemma = ⌜ ΠΣ-distr-≃ ⌝
    Ψ : ℕ → ℕ → 𝟚
    Ψ = pr₁ (lemma σ)
    e = ∃ X                             ≃⟨ ∃-cong pt (pr₂ (lemma σ)) ⟩
        (∃ n ꞉ ℕ , ∃ m ꞉ ℕ , Ψ n m ≡ ₁) ≃⟨ outer-∃-inner-Σ pt        ⟩
        (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁) ■

key-construction : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
                 → (∃ A → Σ Y)
                 → X → X → 𝓤 ⊔ 𝓦 ̇
key-construction {𝓤} {𝓥} {𝓦} {X} {Y} {A} f x y =
  Σ a ꞉ A y , pr₁ (f ∣ y , a ∣) ≡ x

blah : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
     → ((x : X) → is-prop (Y x))
     → (f : (∃ A ≃ (Σ Y)))
     → (x : X) → Y x ≃ ∃ (key-construction ⌜ f ⌝ x)
blah {𝓤} {𝓥} {𝓦} {X} {Y} {A} i f x =
 logically-equivalent-props-are-equivalent (i x) ∥∥-is-prop α β
  where
   β : ∃ (key-construction ⌜ f ⌝ x) → Y x
   β = ∥∥-rec (i x) γ
    where
     γ : Σ (key-construction ⌜ f ⌝ x) → Y x
     γ (y , a , e) = transport Y e (pr₂ (⌜ f ⌝ ∣ y , a ∣))
   α : Y x → ∃ (key-construction ⌜ f ⌝ x)
   α y = ∥∥-functor γ (⌜ f ⌝⁻¹ (x , y))
    where
     γ : Σ A → Σ (key-construction ⌜ f ⌝ x)
     γ (x' , a) = x' , (a , ap pr₁ e)
      where
       e = (⌜ f ⌝ ∣ x' , a ∣)        ≡⟨ ap ⌜ f ⌝ (∥∥-is-prop ∣ x' , a ∣ (⌜ f ⌝⁻¹ (x , y))) ⟩
           (⌜ f ⌝ (⌜ f ⌝⁻¹ (x , y))) ≡⟨ ≃-sym-is-rinv f (x , y) ⟩
           (x , y) ∎

{-
  "All" that's left now is to show that key-construction n m is proposition-valued and decidable.
  This would give that X n is semi-decidable for every n : ℕ.
-}

semidecidability-structure-Σ : (X : ℕ → 𝓤 ̇  )
                             → ((n : ℕ) → is-prop (X n))
                             → semidecidability-structure (Σ X)
                             → (Π n ꞉ ℕ , semidecidability-structure (X n))
semidecidability-structure-Σ X X-is-prop-valued (Ψ , e) n =
 ⌜ semidecidability-structure-≃ ⌝⁻¹ σ
  where
   φ : ℕ → 𝓤₀ ̇
   φ = key-construction ⌜ e ⌝⁻¹ n
   φ-is-prop-valued : (m : ℕ) → is-prop (φ m)
   φ-is-prop-valued m = Σ-is-prop 𝟚-is-set (λ _ → ℕ-is-set)
   φ-is-detachable : detachable φ
   φ-is-detachable m = decidable-closed-under-Σ 𝟚-is-set
                        (𝟚-is-discrete (Ψ m) ₁)
                        (λ (p : Ψ m ≡ ₁) → ℕ-is-discrete (pr₁ (⌜ e ⌝⁻¹ ∣ m , p ∣)) n)
   φ⁺ : ℕ → Ω 𝓤₀
   φ⁺ n = (φ n , φ-is-prop-valued n)
   σ : semidecidability-structure' 𝓤₀ (X n)
   σ = φ⁺ , φ-is-detachable , (blah X-is-prop-valued (≃-sym e) n)

-- Countable-Semidecidable-Choice
Countable-Semidecidability-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Countable-Semidecidability-Choice 𝓤 = (X : ℕ → 𝓤 ̇  )
                                    → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
                                    → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

Semidecidability-Closed-Under-ω-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidability-Closed-Under-ω-Joins 𝓤 = (X : ℕ → 𝓤 ̇  )
                                        → (Π n ꞉ ℕ , is-semidecidable (X n))
                                        → is-semidecidable (∃ X)

csc-implies-that-semidecidability-is-closed-under-ω-joins : {𝓤 : Universe}
 → Countable-Semidecidability-Choice 𝓤
 → Semidecidability-Closed-Under-ω-Joins 𝓤
csc-implies-that-semidecidability-is-closed-under-ω-joins {𝓤} csc X σ =
 ∥∥-functor (∃-has-semidecidability-structure X) (csc X σ)

Semidecidability-Closed-Under-Special-ω-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidability-Closed-Under-Special-ω-Joins 𝓤 = (X : ℕ → 𝓤 ̇  )
                                              → is-prop (Σ X)
                                              → (Π n ꞉ ℕ , is-semidecidable (X n))
                                              → is-semidecidable (Σ X)

Countable-Semidecidability-Special-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Countable-Semidecidability-Special-Choice 𝓤 = (X : ℕ → 𝓤 ̇  )
                                          → is-prop (Σ X)
                                          → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
                                          → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

converse-in-special-cases : {𝓤 : Universe}
                          → Semidecidability-Closed-Under-Special-ω-Joins 𝓤
                          → Countable-Semidecidability-Special-Choice 𝓤
converse-in-special-cases h X i σ =
 ∥∥-functor (semidecidability-structure-Σ X j)
            (h X i σ)
          -- (∥∥-functor (semidecidability-structure-cong e) {!!}) -- (h X i σ))
 where
  j : (n : ℕ) → is-prop (X n)
  j n = prop-if-semidecidable (σ n)
  {-
  e : ∃ X ≃ Σ X
  e = prop-is-equivalent-to-its-truncation i
  -}

\end{code}

TODO:

Countable-Semidecidability-Special-Choice 𝓤

implies that Ωˢᵈ is a dominance, i.e.

semidecidable-closed-under-Σ

\begin{code}



Semidecidable-Closed-Under-Σ : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Closed-Under-Σ 𝓤 𝓥 = (P : 𝓤 ̇  )
                                 → is-semidecidable P
                                 → (Q : P → 𝓥 ̇  )
                                 → ((p : P) → is-semidecidable (Q p))
                                 → is-semidecidable (Σ Q)


-- TODO: Promote this to another equivalent version of semidecidability-structure?
-- TODO: Also add for the version → 𝟚?
least-witness : (A : ℕ → Ω 𝓤)
              → is-decidable-subset A
              → Σ B ꞉ (ℕ → Ω 𝓤) , is-decidable-subset B
                                × ((∃ n ꞉ ℕ , n ∈ A) ≃ (Σ n ꞉ ℕ , n ∈ B))
least-witness {𝓤} A A-is-decidable = B , B-is-decidable , γ
 where
   B : ℕ → Ω 𝓤
   B n = (n ∈ A × is-empty (Σ r ꞉ Fin' n , pr₁ r ∈ A))
       , (×-is-prop (∈-is-prop A n) (negations-are-props fe))
   B-is-decidable : is-decidable-subset B
   B-is-decidable n = ×-preserves-decidability (A-is-decidable n) (¬-preserves-decidability σ)
    where
     σ : decidable (Σ r ꞉ Fin' n , pr₁ r ∈ A)
     σ = Compact-cong (≃-Fin n) Fin-Compact (pr₁ ∘ A ∘ pr₁)
          (λ r → A-is-decidable (pr₁ r))
   ΣB-is-prop : is-prop (Σ n ꞉ ℕ , n ∈ B)
   ΣB-is-prop (n , a , min) (n' , a' , min') =
    to-subtype-≡ (∈-is-prop B) (κ (<-linear n n'))
     where
      κ : (n < n') + (n ≡ n') + (n' < n)
        → n ≡ n'
      κ (inl k)       = 𝟘-elim (min' ((n , k) , a))
      κ (inr (inl e)) = e
      κ (inr (inr l)) = 𝟘-elim (min ((n' , l) , a'))
   γ : (∃ n ꞉ ℕ , n ∈ A) ≃ (Σ n ꞉ ℕ , n ∈ B)
   γ = logically-equivalent-props-are-equivalent ∥∥-is-prop ΣB-is-prop f g
    where
     g : (Σ n ꞉ ℕ , n ∈ B) → (∃ n ꞉ ℕ , n ∈ A)
     g (n , a , _) = ∣ n , a ∣
     f : (∃ n ꞉ ℕ , n ∈ A) → (Σ n ꞉ ℕ , n ∈ B)
     f = ∥∥-rec ΣB-is-prop h
      where
       h : (Σ n ꞉ ℕ , n ∈ A) → (Σ n ꞉ ℕ , n ∈ B)
       h (n , a) = k , a' , ν
        where
         u : Σμ (λ m → m ∈ A)
         u = minimal-from-given (λ m → m ∈ A) A-is-decidable (n , a)
         k : ℕ
         k = pr₁ u
         a' : k ∈ A
         a' = pr₁ (pr₂ u)
         min : (m : ℕ) → m ∈ A → k ≤ m
         min = pr₂ (pr₂ u)
         ν : is-empty (Σ r ꞉ Fin' k , pr₁ r ∈ A)
         ν ((m , l) , aₘ) = less-not-bigger-or-equal m k l (min m aₘ)

\end{code}

We should now have enough...

\begin{code}

semidecidable-closed-under-Σ : Semidecidability-Closed-Under-Special-ω-Joins 𝓤
                             → Semidecidable-Closed-Under-Σ 𝓥 𝓤
semidecidable-closed-under-Σ {𝓤} H P ρ Q σ = ∥∥-rec being-semidecidable-is-prop γ ρ
 where
  γ : semidecidability-structure P
    → is-semidecidable (Σ Q)
  γ (α , e) = is-semidecidable-cong ΣQ₂-ΣQ-equiv ΣQ₂-is-semidecidable
   where
    Q-is-prop-valued : (p : P) → is-prop (Q p)
    Q-is-prop-valued p = prop-if-semidecidable (σ p)

    W : Σ B ꞉ (ℕ → Ω 𝓤₀) , is-decidable-subset B
                         × ((∃ n ꞉ ℕ , α n ≡ ₁) ≃ (Σ n ꞉ ℕ , n ∈ B))
    W = least-witness (λ n → (α n ≡ ₁) , 𝟚-is-set) (λ n → 𝟚-is-discrete (α n) ₁)

    Q₁ : ℕ → Ω 𝓤₀
    Q₁ = pr₁ W
    Q₁-is-decidable : is-decidable-subset Q₁
    Q₁-is-decidable = pr₁ (pr₂ W)
    ΣQ₁-equiv : (∃ n ꞉ ℕ , α n ≡ ₁) ≃ (Σ n ꞉ ℕ , n ∈ Q₁)
    ΣQ₁-equiv = pr₂ (pr₂ W)
    ΣQ₁-to-P : (Σ n ꞉ ℕ , n ∈ Q₁) → P
    ΣQ₁-to-P = ⌜ e ⌝⁻¹ ∘ ⌜ ΣQ₁-equiv ⌝⁻¹

    Q₂ : ℕ → 𝓤 ̇
    Q₂ n = Σ q ꞉ n ∈ Q₁ , Q (ΣQ₁-to-P (n , q))
    Q₂-is-prop-valued : (n : ℕ) → is-prop (Q₂ n)
    Q₂-is-prop-valued n = Σ-is-prop (∈-is-prop Q₁ n)
                           (λ q₁ → Q-is-prop-valued (ΣQ₁-to-P (n , q₁)))

    ΣQ₂-is-prop : is-prop (Σ Q₂)
    ΣQ₂-is-prop (n , q₁ , q) (n' , q₁' , q') =
     to-subtype-≡ Q₂-is-prop-valued
                  (ap pr₁ (equiv-to-prop (≃-sym ΣQ₁-equiv) ∥∥-is-prop
                            (n , q₁) (n' , q₁')))
    ΣQ₂-ΣQ-equiv : Σ Q₂ ≃ Σ Q
    ΣQ₂-ΣQ-equiv = logically-equivalent-props-are-equivalent ΣQ₂-is-prop
                    (Σ-is-prop (prop-if-semidecidable ρ)
                    (λ p → prop-if-semidecidable (σ p)))
                    f g
     where
      f : Σ Q₂ → Σ Q
      f (n , q₁ , q) = (ΣQ₁-to-P (n , q₁) , q)
      g : Σ Q → Σ Q₂
      g (p , q) = (n , q₁ , transport Q (prop-if-semidecidable ρ p p') q)
       where
        n : ℕ
        n = pr₁ (⌜ ΣQ₁-equiv ⌝ (⌜ e ⌝ p))
        q₁ : n ∈ Q₁
        q₁ = pr₂ (⌜ ΣQ₁-equiv ⌝ (⌜ e ⌝ p))
        p' : P
        p' = ΣQ₁-to-P (n , q₁)

    ΣQ₂-is-semidecidable : is-semidecidable (Σ Q₂)
    ΣQ₂-is-semidecidable = H Q₂ ΣQ₂-is-prop τ
     where
      τ : (n : ℕ) → is-semidecidable (Q₂ n)
      τ n = κ (Q₁-is-decidable n)
       where
        κ : decidable (n ∈ Q₁) → is-semidecidable (Q₂ n)
        κ (inl  q₁) = is-semidecidable-cong claim (σ p)
         where
          p : P
          p = ΣQ₁-to-P (n , q₁)
          claim : Q p ≃ Q₂ n
          claim = logically-equivalent-props-are-equivalent
                   (Q-is-prop-valued p) (Q₂-is-prop-valued n)
                   ϕ ψ
           where
            ϕ : Q p → Q₂ n
            ϕ q = q₁ , q
            ψ : Q₂ n → Q p
            ψ (q₁ , q) =
             transport Q (prop-if-semidecidable ρ (ΣQ₁-to-P (n , q₁)) p) q
        κ (inr nq₁) = empty-types-are-semidecidable claim
         where
          claim : is-empty (Q₂ n)
          claim (q₁ , q) = nq₁ q₁

Escardo-Knapp-Choice : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Escardo-Knapp-Choice 𝓤 𝓥 = (P : 𝓤 ̇  ) (Q : 𝓥 ̇  )
                         → is-semidecidable P
                         → (P → is-semidecidable Q)
                         → ∥ (P → semidecidability-structure Q) ∥

theorem-3-1 : Semidecidable-Closed-Under-Σ 𝓤 𝓥
            → Escardo-Knapp-Choice 𝓤 𝓥
theorem-3-1 H P Q ρ σ = ∥∥-functor g τ
 where
  τ : is-semidecidable (P × Q)
  τ = H P ρ (λ _ → Q) σ
  f : P → (P × Q) ≃ Q
  f p = logically-equivalent-props-are-equivalent
         (×-is-prop (prop-if-semidecidable ρ) Q-is-prop) Q-is-prop
          pr₂ (λ q → p , q)
   where
    Q-is-prop : is-prop Q
    Q-is-prop = prop-if-semidecidable (σ p)
  g : semidecidability-structure (P × Q) → (P → semidecidability-structure Q)
  g 𝕤 p = semidecidability-structure-cong (f p) 𝕤

\end{code}

\begin{code}



Semidecidable-Dominance-Axiom : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Dominance-Axiom 𝓤 𝓥 = (P : 𝓤 ̇  )
                                  → is-semidecidable P
                                  → (Q : 𝓥 ̇  )
                                  → (P → is-semidecidable Q)
                                  → is-semidecidable (P × Q)

-- TODO: Reorganize using Dominance?
closure-under-Σ-criterion : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
                          → Semidecidable-Closed-Under-Σ 𝓤 𝓥
closure-under-Σ-criterion {𝓤} {𝓥} D P ρ Q σ = τ
 where
  i : is-prop P
  i = prop-if-semidecidable ρ
  j : (p : P) → is-prop (Q p)
  j p = prop-if-semidecidable (σ p)
  Q' : 𝓤 ⊔ 𝓥 ̇
  Q' = Σ Q
  k : is-prop Q'
  k = Σ-is-prop i j
  e : (p : P) → Q' ≃ Q p
  e p = logically-equivalent-props-are-equivalent k (j p)
         (λ (p' , q) → transport Q (i p' p) q)
         (λ q → p , q)
  τ : is-semidecidable (Σ Q)
  τ = is-semidecidable-cong (Σ-cong e) (D P ρ Q' τ')
   where
    τ' : P → is-semidecidable Q'
    τ' p = is-semidecidable-cong (≃-sym (e p)) (σ p)

theorem-3-1-converse : Escardo-Knapp-Choice 𝓤 (𝓤 ⊔ 𝓥)
                     → Semidecidable-Closed-Under-Σ 𝓤 𝓥
theorem-3-1-converse {𝓤} {𝓥} ekc = closure-under-Σ-criterion γ
 where
  γ : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
  γ P ρ Q σ = ∥∥-rec being-semidecidable-is-prop r ρ
   where
    r : semidecidability-structure P → is-semidecidable (P × Q)
    r (α , e) = ∥∥-functor s (ekc P Q ρ σ)
     where
      to-P : (∃ n ꞉ ℕ , α n ≡ ₁) → P
      to-P = ⌜ e ⌝⁻¹
      s : (P → semidecidability-structure Q)
        → semidecidability-structure (P × Q)
      s σ⁺ = ⌜ semidecidability-pairing-lemma ⌝ τ
       where
        β : P → (ℕ → 𝟚)
        β p = pr₁ (σ⁺ p)
        φ : ℕ × ℕ → 𝓤₀ ̇
        φ (n , m) = Σ b ꞉ α n ≡ ₁ , β (to-P ∣ n , b ∣) m ≡ ₁
        φ-is-detachable : detachable φ
        φ-is-detachable (n , m) = decidable-closed-under-Σ
                                   𝟚-is-set
                                   (𝟚-is-discrete (α n) ₁)
                                   (λ b → 𝟚-is-discrete (β (to-P ∣ n , b ∣) m) ₁)
        φ-is-prop-valued : (k : ℕ × ℕ) → is-prop (φ k)
        φ-is-prop-valued k = Σ-is-prop 𝟚-is-set (λ b → 𝟚-is-set)
        φ⁺ : ℕ × ℕ → Ω 𝓤₀
        φ⁺ k = φ k , φ-is-prop-valued k

        τ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁)
        τ = ⌜ uncurry-lemma ⌝ τ'
         where
          uncurry-lemma :
             (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ (n , m) ≡ ₁))
           ≃ (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁))
          uncurry-lemma = ≃-sym
                           (Σ-change-of-variable _ ⌜ μ ⌝⁻¹ (⌜⌝⁻¹-is-equiv μ))
           where
            μ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
            μ = curry-uncurry fe'

          τ' : (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
          τ' = Ψ , (P × Q                              ≃⟨ I  ⟩
                   (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m))     ≃⟨ II ⟩
                   (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁) ■)
           where
            χ : (Σ A ꞉ (ℕ × ℕ → Ω 𝓤₀) , is-decidable-subset A) → (ℕ × ℕ → 𝟚)
            χ = ⌜ 𝟚-classifies-decidable-subsets fe fe pe ⌝⁻¹
            Ψ : ℕ × ℕ → 𝟚
            Ψ = χ (φ⁺ , φ-is-detachable)

            II = ∥∥-cong pt (Σ-cong (λ n → Σ-cong
                                    (λ m → logically-equivalent-props-are-equivalent
                                           (φ-is-prop-valued (n , m))
                                           𝟚-is-set
                                           (rl-implication (lemma n m))
                                           (lr-implication (lemma n m)))))
             where
              lemma : (n m : ℕ) → χ (φ⁺ , φ-is-detachable) (n , m) ≡ ₁ ⇔ (n , m) ∈ φ⁺
              lemma n m = pr₂ (𝟚-classifies-decidable-subsets-values fe fe pe
                                φ⁺ φ-is-detachable (n , m))
            I  = logically-equivalent-props-are-equivalent j ∥∥-is-prop f g
             where
              j : is-prop (P × Q)
              j = prop-criterion
                   (λ (p , q) → ×-is-prop (prop-if-semidecidable ρ)
                                          (prop-if-semidecidable (σ p)))
              e' : (p : P) → Q ≃ (∃ m ꞉ ℕ , β p m ≡ ₁)
              e' p = pr₂ (σ⁺ p)
              g : (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
              g = ∥∥-rec j g'
               where
                g' : (Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
                g' (n , m , b , b') = p , ⌜ e' p ⌝⁻¹ ∣ m , b' ∣
                 where
                  p : P
                  p = to-P ∣ n , b ∣
              f : P × Q → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
              f (p , q) = ∥∥-rec ∥∥-is-prop f' (⌜ e ⌝ p)
               where
                f' : (Σ n ꞉ ℕ , α n ≡ ₁)
                   → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
                f' (n , b) = ∥∥-functor f'' (⌜ e' p' ⌝ q)
                 where
                  p' : P
                  p' = to-P ∣ n , b ∣
                  f'' : (Σ m ꞉ ℕ , β p' m ≡ ₁)
                      → (Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m))
                  f'' (m , b') = n , m , b , b'

\end{code}

Summary:

   EKCˢᵈ <=> Dominance Axiom
    ^                     ^
    |                     |
    |                     |
Special CC <=> Special ω-joins in Ωˢᵈ
    ^                     ^
    |                     |
    |                     |
Semidecidable CC ==> ω-joins in Ωˢᵈ

The conjecture is that ω-joins in Ωˢᵈ is equivalent to some form of countable choice. But which?!

Discussion:

 * Ωˢᵈ is closed under finitary (nullary + binary) joins
 * Ωˢᵈ is closed under finitary (nullary + binary) meets
 * LPO <=> Ωˢᵈ ≃ 𝟚.
 * If LPO holds, then Ωˢᵈ is closed under negation.

   The converse holds if we assume Markov's Principle (MP), which says that
   every semidecidable proposition is ¬¬-stable:
     Assume MP and that Ωˢᵈ is closed under negation.
     We show that LPO holds, i.e. every semidecidable proposition is decidable.
     Let X be semidecidable. By assumption so is ¬ X. We prove that X is
     decidable following the proof of Theorem 3.21 of Bauer's "First Steps in
     Synthetic Computability Theory": note (X + ¬ X) ∈ Ωˢᵈ, so by MP it is
     ¬¬-stable, but ¬¬ (X + ¬ X) is a theorem of constructive logic, so X is
     decidable.                                                                 □

 * TODO: Think about implication

\begin{code}

MP : 𝓤₀ ̇
MP = (α : ℕ → 𝟚) → ¬¬-stable (∃ n ꞉ ℕ , α n ≡ ₁)

MP-is-prop : is-prop MP
MP-is-prop = Π₂-is-prop fe (λ α h → ∥∥-is-prop)

MP' : (𝓤 : Universe) → 𝓤 ⁺ ̇
MP' 𝓤 = ((X : 𝓤 ̇  ) → is-semidecidable X → ¬¬-stable X)

MP'-is-prop : {𝓤 : Universe} → is-prop (MP' 𝓤)
MP'-is-prop = Π₃-is-prop fe (λ X σ h → prop-if-semidecidable σ)

¬¬-stable-⇔ : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
            → X ⇔ Y
            → ¬¬-stable X
            → ¬¬-stable Y
¬¬-stable-⇔ (f , g) σ h = f (σ (¬¬-functor g h))

¬¬-stable-≃ : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
            → X ≃ Y
            → ¬¬-stable X
            → ¬¬-stable Y
¬¬-stable-≃ e = ¬¬-stable-⇔ (⌜ e ⌝ , ⌜ e ⌝⁻¹)

MP-equivalence : {𝓤 : Universe}
               → MP ≃ MP' 𝓤
MP-equivalence {𝓤} = logically-equivalent-props-are-equivalent
                           MP-is-prop MP'-is-prop f g
 where
  f : MP → MP' 𝓤
  f mp X σ nnX = ∥∥-rec (prop-if-semidecidable σ) γ σ
   where
    γ : semidecidability-structure X → X
    γ (α , e) = ⌜ e ⌝⁻¹ (mp α (¬¬-functor ⌜ e ⌝ nnX))
  g : MP' 𝓤 → MP
  g τ α = ¬¬-stable-≃ (Lift-≃ 𝓤 X) (τ X' σ')
   where
    X : 𝓤₀ ̇
    X = ∃ n ꞉ ℕ , α n ≡ ₁
    X' : 𝓤 ̇
    X' = Lift 𝓤 X
    σ' : is-semidecidable X'
    σ' = is-semidecidable-cong (≃-sym (Lift-≃ 𝓤 X)) ∣ α , ≃-refl X ∣

all-types-are-¬¬-decidable : (X : 𝓤 ̇  ) → ¬¬ (decidable X)
all-types-are-¬¬-decidable X h = claim₂ claim₁
 where
  claim₁ : ¬ X
  claim₁ x = h (inl x)
  claim₂ : ¬¬ X
  claim₂ nx = h (inr nx)

LPO-from-semidecidable-negations : MP' 𝓤
                                 → Semidecidable-Closed-Under-Negations 𝓤
                                 → LPO' 𝓤
LPO-from-semidecidable-negations mp h X σ = mp (decidable X) τ
                                             (all-types-are-¬¬-decidable X)
 where
  τ : is-semidecidable (decidable X)
  τ = decidability-is-semidecidable X σ (h X σ)

{-

  Assume MP and Ωˢᵈ closed under ¬.

  Suppose X is semidecidable, then so is ¬ X. Hence, (X + ¬ X) is semidecidable.
  But ¬¬ (X + ¬ X) just holds. By MP: ¬¬ Y → Y for every semidecidable Y.
  Hence, (X + ¬ X) which is LPO.


-}





LPO-≃-semidecidable-negations : MP' 𝓤
                              → LPO' 𝓤 ≃ Semidecidable-Closed-Under-Negations 𝓤
LPO-≃-semidecidable-negations mp =
 logically-equivalent-props-are-equivalent
  LPO'-is-prop
  (Π₂-is-prop fe (λ X σ → being-semidecidable-is-prop))
  semidecidable-negations-from-LPO
  (LPO-from-semidecidable-negations mp)

\end{code}

\begin{code}

Semidecidable-Closed-Under-Implications : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Closed-Under-Implications 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : 𝓥 ̇  )
                                            → is-semidecidable X
                                            → is-semidecidable Y
                                            → is-semidecidable (X → Y)

LPO-from-semidecidable-implications : MP' 𝓤
                                    → Semidecidable-Closed-Under-Implications 𝓤 𝓤₀
                                    → LPO' 𝓤
LPO-from-semidecidable-implications mp h =
 LPO-from-semidecidable-negations mp (λ X σ → h X 𝟘 σ 𝟘-is-semidecidable)



semidecidable-implications-from-LPO : LPO' 𝓤
                                    → Semidecidable-Closed-Under-Implications 𝓤 𝓤₀
semidecidable-implications-from-LPO lpo X Y σ τ =
 semidecidable-if-decidable-prop
  (Π-is-prop fe (λ _ → prop-if-semidecidable τ))
  (→-preserves-decidability (lpo X σ) (⌜ LPO-across-universes ⌝ lpo Y τ))

\end{code}

See also CantorSchroederBernstein.lagda by Martín.

BKS⁺ ⇔ (Ωˢᵈ ≃ Ω)

EM   ⇔ (𝟚 ≃ Ωˢᵈ ≃ Ω)

We have: Ωˢᵈ has all suprema ⇔ BKS⁺.
Hence, BKS⁺ implies the above instance of special countable choice.

We also have: BKS⁺ ⇒ Ωˢᵈ has all infima ⇒ (MP ⇒ LPO).

\begin{code}

BKS⁺ : (𝓤 : Universe) → (𝓤 ⁺) ̇
BKS⁺ 𝓤 = (X : 𝓤 ̇  ) → is-prop X → is-semidecidable X -- Ωˢᵈ ≃ Ω

open import UF-ExcludedMiddle

BKS⁺→LPO→EM : {𝓤 : Universe} → BKS⁺ 𝓤 → LPO' 𝓤 → EM 𝓤
BKS⁺→LPO→EM {𝓤} bks lpo X X-is-prop = lpo X (bks X X-is-prop)

-- In CantorSchroederBernstein.lagda, we have: BKS⁺ 𝓤 → MP' 𝓤 → EM 𝓤

Semidecidable-All-Meets : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-All-Meets 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  )
                            → ((x : X) → is-semidecidable (Y x))
                            → is-semidecidable (Π Y)

all-meets-implies-negations : Semidecidable-All-Meets 𝓤 𝓤₀
                            → Semidecidable-Closed-Under-Negations 𝓤
all-meets-implies-negations h X _ = h X (λ _ → 𝟘) (λ _ → 𝟘-is-semidecidable)

all-meets-implies-LPO : Semidecidable-All-Meets 𝓤 𝓤₀
                      → MP' 𝓤
                      → LPO' 𝓤
all-meets-implies-LPO h mp = LPO-from-semidecidable-negations mp (all-meets-implies-negations h)

{-
Π-preserves-decidability : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
                         → is-prop A
                         → decidable A
                         → ((a : A) → decidable (B a))
                         → decidable (Π B)
Π-preserves-decidability {𝓤} {𝓥} {A} {B} i (inl  a) h = γ (h a)
 where
  γ : decidable (B a) → decidable (Π B)
  γ (inl  b) = inl (λ a' → transport B (i a a') b)
  γ (inr nb) = inr (λ f → nb (f a))
Π-preserves-decidability _ (inr na) _ = inl (λ a → 𝟘-elim (na a))
-}

BKS⁺-implies-all-meets : BKS⁺ (𝓤 ⊔ 𝓥)
                       → Semidecidable-All-Meets 𝓤 𝓥
BKS⁺-implies-all-meets bks X Y σ = bks (Π Y) (Π-is-prop fe (λ x → prop-if-semidecidable (σ x)))

Semidecidable-All-Joins : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-All-Joins 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  )
                            → ((x : X) → is-semidecidable (Y x))
                            → is-semidecidable (∃ Y)

BKS⁺-implies-all-joins : BKS⁺ (𝓤 ⊔ 𝓥)
                       → Semidecidable-All-Joins 𝓤 𝓥
BKS⁺-implies-all-joins bks X Y σ = bks (∃ Y) ∥∥-is-prop

-- TODO: Arbitrary subsingleton joins suffice
-- Implemented now:
Semidecidable-Subsingleton-Joins : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Subsingleton-Joins 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  ) → is-prop X
                                     → ((x : X) → is-semidecidable (Y x))
                                     → is-semidecidable (∃ Y)

subsingleton-joins-implies-BKS⁺ : Semidecidable-Subsingleton-Joins 𝓤 𝓤₀
                                → BKS⁺ 𝓤
subsingleton-joins-implies-BKS⁺ σ X X-is-prop =
 is-semidecidable-cong γ (σ X (λ _ → 𝟙) X-is-prop (λ _ → 𝟙-is-semidecidable))
  where
   γ : ∥ X × 𝟙 ∥ ≃ X
   γ = ∥ X × 𝟙 ∥ ≃⟨ ∥∥-cong pt 𝟙-rneutral ⟩
       ∥ X ∥     ≃⟨ prop-is-equivalent-to-its-truncation X-is-prop ⟩
       X         ■

all-joins-implies-BKS⁺ : Semidecidable-All-Joins 𝓤 𝓤₀
                       → BKS⁺ 𝓤
all-joins-implies-BKS⁺ j =
 subsingleton-joins-implies-BKS⁺ (λ X Y X-is-prop σ → j X Y σ)

BKS⁺-implies-special-countable-choice : BKS⁺ 𝓤
                                      → Countable-Semidecidability-Special-Choice 𝓤
BKS⁺-implies-special-countable-choice {𝓤} bks = converse-in-special-cases γ
 where
  γ : Semidecidability-Closed-Under-Special-ω-Joins 𝓤
  γ X i σ = bks (Σ X) i

-- TODO: Hence, BKS⁺ → EKC.
-- Is there a quick direct proof of this?

-- Answer: Yes (of course), using Theorem 3.1.

\end{code}

\begin{code}

BKS⁺-implies-EKCˢᵈ : BKS⁺ (𝓤 ⊔ 𝓥)
                   → Escardo-Knapp-Choice 𝓤 𝓥
BKS⁺-implies-EKCˢᵈ bks = theorem-3-1 (λ P σ Q τ → bks (Σ Q) (Σ-is-prop (prop-if-semidecidable σ) (λ p → prop-if-semidecidable (τ p))))

\end{code}

Notice that BKS⁺ implies propositional resizing.

\begin{code}

open import UF-Size

BKS⁺-gives-Propositional-Resizing : BKS⁺ 𝓤
                                  → propositional-resizing 𝓤 𝓤₀
BKS⁺-gives-Propositional-Resizing bks X X-is-prop =
 ∥∥-rec (prop-has-size-is-prop (λ _ → pe) fe' X X-is-prop 𝓤₀) γ (bks X X-is-prop)
  where
   γ : semidecidability-structure X → X has-size 𝓤₀
   γ (α , e) = (∃ n ꞉ ℕ , α n ≡ ₁) , (≃-sym e)

\end{code}
