Tom de Jong & Martín Escardó, 4 April 2022.

TODO

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

module UF-Quotient-Axiomatically where

open import UF-Equiv
open import UF-ImageAndSurjection
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Size

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued    _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_ × reflexive  _≈_
                      × symmetric      _≈_ × transitive _≈_

EqRel : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
EqRel {𝓤} {𝓥} X = Σ R ꞉ (X → X → 𝓥 ̇ ) , is-equiv-relation R

_≈[_]_ : {X : 𝓤 ̇ } → X → EqRel X → X → 𝓥 ̇
x ≈[ _≈_ , _ ] y = x ≈ y

identifies-related-points : {X : 𝓤 ̇  } (≈ : EqRel {𝓤} {𝓥} X) {Y : 𝓦 ̇  }
                          → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
identifies-related-points (_≈_ , _) f = ∀ {x x'} → x ≈ x' → f x ≡ f x'

record set-quotients-exist : 𝓤ω where
 field
  _/_ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇  ) → EqRel {𝓤} {𝓥} X → 𝓤 ⊔ 𝓥 ̇
  η/ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X) → X → X / ≋
  η/-identifies-related-points : {𝓤 𝓥 : Universe}
                                 {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
                               → identifies-related-points ≋ (η/ ≋)
  /-is-set : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X) → is-set (X / ≋)
  /-induction : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
              → {P : X / ≋ → 𝓦 ̇  } → ((x : X) → P (η/ ≋ x)) → (y : X / ≋) → P y
  /-universality : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
                 → {Y : 𝓦 ̇  } → is-set Y → (f : X → Y)
                 → identifies-related-points ≋ f
                 → ∃! f̅ ꞉ (X / ≋ → Y) , f̅ ∘ η/ ≋ ∼ f

 module _
         {X : 𝓤 ̇  }
         (≋ : EqRel {𝓤} {𝓥} X)
        where

  module _
          {A : 𝓦 ̇  }
          (A-is-set : is-set A)
         where

   mediating-map/ : (f : X → A)
                  → identifies-related-points ≋ f
                  → X / ≋ → A
   mediating-map/ f p = ∃!-witness (/-universality ≋ A-is-set f p)

   universality-triangle/ : (f : X → A)
                            (p : identifies-related-points ≋ f)
                          → mediating-map/ f p ∘ η/ ≋ ∼ f
   universality-triangle/ f p = ∃!-is-witness (/-universality ≋ A-is-set f p)


 quotients-equivalent : (X : 𝓤 ̇ ) (R : EqRel {𝓤} {𝓥} X) (R' : EqRel {𝓤} {𝓦} X)
                      → ({x y : X} → x ≈[ R ] y ⇔ x ≈[ R' ] y)
                      → (X / R) ≃ (X / R')
 quotients-equivalent X (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
                        (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t') ε = γ
  where
   ≋  = (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
   ≋' = (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t')
   i : {x y : X} → x ≈ y → η/ ≋' x ≡ η/ ≋' y
   i e = η/-identifies-related-points ≋' (lr-implication ε e)
   i' : {x y : X} → x ≈' y → η/ ≋ x ≡ η/ ≋ y
   i' e = η/-identifies-related-points ≋ (rl-implication ε e)
   f : X / ≋ → X / ≋'
   f = mediating-map/ ≋ (/-is-set ≋') (η/ ≋') i
   f' : X / ≋' → X / ≋
   f' = mediating-map/ ≋' (/-is-set ≋) (η/ ≋) i'
   a : (x : X) → f (f' (η/ ≋' x)) ≡ η/ ≋' x
   a x = f (f' (η/ ≋' x)) ≡⟨ I ⟩
         f (η/ ≋ x)       ≡⟨ II ⟩
         η/ ≋' x          ∎
    where
     I  = ap f (universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x)
     II = universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x
   α : f ∘ f' ∼ id
   α = /-induction ≋' a
   a' : (x : X) → f' (f (η/ ≋ x)) ≡ η/ ≋ x
   a' x = f' (f (η/ ≋ x)) ≡⟨ I ⟩
         f' (η/ ≋' x)     ≡⟨ II ⟩
         η/ ≋ x           ∎
    where
     I  = ap f' (universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x)
     II = universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x
   α' : f' ∘ f ∼ id
   α' = /-induction ≋ a'
   γ : (X / ≋) ≃ (X / ≋')
   γ = qinveq f (f' , α' , α)

\end{code}

\begin{code}

 private
  module _ {X : 𝓤 ̇  } where
   _≈_ : X → X → 𝓤₀ ̇
   x ≈ y = 𝟙
   ≋ : EqRel X
   ≋ = _≈_ , (λ x y → 𝟙-is-prop) , (λ x → ⋆) , (λ x y _ → ⋆) , (λ x y z _ _ → ⋆)

  ∥_∥ : 𝓤 ̇  → 𝓤 ̇
  ∥_∥ X = X / ≋

  ∣_∣ : {X : 𝓤 ̇  } → X → ∥ X ∥
  ∣_∣ = η/ ≋

  ∥∥-is-prop : {X : 𝓤 ̇  } → is-prop ∥ X ∥
  ∥∥-is-prop = /-induction ≋ (λ x → /-induction ≋
                             (λ y → η/-identifies-related-points ≋ ⋆))

  ∥∥-rec : {X : 𝓤 ̇  } {P : 𝓥 ̇  } → is-prop P → (X → P) → ∥ X ∥ → P
  ∥∥-rec {𝓤} {𝓥} {X} {P} i f =
   ∃!-witness (/-universality ≋ (props-are-sets i) f
                              (λ {x} {x'}_ → i (f x) (f x')))

 propositional-truncations-from-axiomatic-quotients :
  propositional-truncations-exist
 propositional-truncations-from-axiomatic-quotients = record {
    ∥_∥        = ∥_∥
  ; ∥∥-is-prop = ∥∥-is-prop
  ; ∣_∣        = ∣_∣
  ; ∥∥-rec     = ∥∥-rec
  }

module _ (sq : set-quotients-exist) where
 open set-quotients-exist sq

 private
  pt = propositional-truncations-from-axiomatic-quotients

 open Replacement pt
 open PropositionalTruncation pt

 module replacement-construction
         {X : 𝓤 ̇  }
         {Y : 𝓦 ̇  }
         (f : X → Y)
         (Y-is-loc-small : Y is-locally 𝓥 small)
         (Y-is-set : is-set Y)
        where

  _≈_ : X → X → 𝓦 ̇
  x ≈ x' = f x ≡ f x'

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued x x' = Y-is-set

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive x = refl

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric x x' p = p ⁻¹

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive _ _ _ p q = p ∙ q

  ≈-is-equiv-rel : is-equiv-relation _≈_
  ≈-is-equiv-rel = ≈-is-prop-valued , ≈-is-reflexive  ,
                   ≈-is-symmetric   , ≈-is-transitive

 \end{code}

 Using that Y is locally 𝓥 small, we resize _≈_ to a 𝓥-valued equivalence
 relation.

 \begin{code}

  _≈⁻_ : X → X → 𝓥 ̇
  x ≈⁻ x' = pr₁ (Y-is-loc-small (f x) (f x'))

  ≈⁻-≃-≈ : {x x' : X} → x ≈⁻ x' ≃ x ≈ x'
  ≈⁻-≃-≈ {x} {x'} = pr₂ (Y-is-loc-small (f x) (f x'))

  ≈⁻-is-prop-valued : is-prop-valued _≈⁻_
  ≈⁻-is-prop-valued x x' = equiv-to-prop ≈⁻-≃-≈ (≈-is-prop-valued x x')

  ≈⁻-is-reflexive : reflexive _≈⁻_
  ≈⁻-is-reflexive x = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-reflexive x)

  ≈⁻-is-symmetric : symmetric _≈⁻_
  ≈⁻-is-symmetric x x' p = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-symmetric x x' (⌜ ≈⁻-≃-≈ ⌝ p))

  ≈⁻-is-transitive : transitive _≈⁻_
  ≈⁻-is-transitive x x' x'' p q =
   ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-transitive x x' x'' (⌜ ≈⁻-≃-≈ ⌝ p) (⌜ ≈⁻-≃-≈ ⌝ q))

  ≈⁻-is-equiv-rel : is-equiv-relation _≈⁻_
  ≈⁻-is-equiv-rel = ≈⁻-is-prop-valued , ≈⁻-is-reflexive  ,
                    ≈⁻-is-symmetric   , ≈⁻-is-transitive

  ≋ : EqRel X
  ≋ = _≈_ , ≈-is-equiv-rel

  X/≈ : 𝓤 ⊔ 𝓦 ̇
  X/≈ = (X / ≋)

  X/≈⁻ : 𝓤 ⊔ 𝓥 ̇
  X/≈⁻ = (X / (_≈⁻_ , ≈⁻-is-equiv-rel))

  [_] : X → X/≈
  [_] = η/ ≋

  X/≈-≃-X/≈⁻ : X/≈ ≃ X/≈⁻
  X/≈-≃-X/≈⁻ = quotients-equivalent X ≋ (_≈⁻_ , ≈⁻-is-equiv-rel)
                                        (⌜ ≈⁻-≃-≈ ⌝⁻¹ , ⌜ ≈⁻-≃-≈ ⌝)

 \end{code}

 We now proceed to show that X/≈ and image f are equivalent types.

 \begin{code}

  corestriction-respects-≈ : {x x' : X}
                           → x ≈ x'
                           → corestriction f x ≡ corestriction f x'
  corestriction-respects-≈ =
   to-subtype-≡ (λ y → being-in-the-image-is-prop y f)

  quotient-to-image : X/≈ → image f
  quotient-to-image = mediating-map/ ≋ (image-is-set f Y-is-set)
                       (corestriction f) (corestriction-respects-≈)

  image-to-quotient' : (y : image f)
                     → Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ pr₁ y)
  image-to-quotient' (y , p) = ∥∥-rec prp r p
   where
    r : (Σ x ꞉ X , f x ≡ y)
      → (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
    r (x , e) = [ x ] , ∣ x , refl , e ∣
    prp : is-prop (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
    prp (q , u) (q' , u') = to-subtype-≡ (λ _ → ∃-is-prop)
                                         (∥∥-rec₂ (/-is-set ≋) γ u u')
     where
      γ : (Σ x  ꞉ X , ([ x  ] ≡ q ) × (f x  ≡ y))
        → (Σ x' ꞉ X , ([ x' ] ≡ q') × (f x' ≡ y))
        → q ≡ q'
      γ (x , refl , e) (x' , refl , refl) = η/-identifies-related-points ≋ e

  image-to-quotient : image f → X/≈
  image-to-quotient y = pr₁ (image-to-quotient' y)

  image-to-quotient-lemma : (x : X)
                          → image-to-quotient (corestriction f x) ≡ [ x ]
  image-to-quotient-lemma x = ∥∥-rec (/-is-set ≋) γ t
   where
    q : X/≈
    q = image-to-quotient (corestriction f x)
    t : ∃ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x)
    t = pr₂ (image-to-quotient' (corestriction f x))
    γ : (Σ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x))
      → q ≡ [ x ]
    γ (x' , u , v) =   q    ≡⟨ u ⁻¹ ⟩
                     [ x' ] ≡⟨ η/-identifies-related-points ≋ v ⟩
                     [ x  ] ∎

  image-≃-quotient : image f ≃ X/≈
  image-≃-quotient = qinveq ϕ (ψ , ρ , σ)
   where
    ϕ : image f → X/≈
    ϕ = image-to-quotient
    ψ : X/≈ → image f
    ψ = quotient-to-image
    τ : (x : X) → ψ [ x ] ≡ corestriction f x
    τ = universality-triangle/ ≋ (image-is-set f Y-is-set)
                               (corestriction f)
                               corestriction-respects-≈
    σ : ϕ ∘ ψ ∼ id
    σ = /-induction ≋ γ
     where
      γ : (x : X) → ϕ (ψ [ x ]) ≡ [ x ]
      γ x = ϕ (ψ [ x ])            ≡⟨ ap ϕ (τ x)                ⟩
            ϕ (corestriction f x ) ≡⟨ image-to-quotient-lemma x ⟩
            [ x ]                  ∎
    ρ : ψ ∘ ϕ ∼ id
    ρ (y , p) = ∥∥-rec (image-is-set f Y-is-set) γ p
     where
      γ : (Σ x ꞉ X , f x ≡ y) → ψ (ϕ (y , p)) ≡ (y , p)
      γ (x , refl) = ψ (ϕ (f x , p))           ≡⟨ ⦅1⦆ ⟩
                     ψ (ϕ (corestriction f x)) ≡⟨ ⦅2⦆ ⟩
                     ψ [ x ]                   ≡⟨ ⦅3⦆ ⟩
                     corestriction f x         ≡⟨ ⦅4⦆ ⟩
                     (f x , p)                 ∎
       where
        ⦅4⦆ = to-subtype-≡ (λ y → being-in-the-image-is-prop y f) refl
        ⦅1⦆ = ap (ψ ∘ ϕ) (⦅4⦆ ⁻¹)
        ⦅2⦆ = ap ψ (image-to-quotient-lemma x)
        ⦅3⦆ = τ x

 replacement-from-axiomatic-quotients : Replacement
 replacement-from-axiomatic-quotients {𝓤} {𝓦} {𝓥} {X} {Y} f
                                      Y-is-loc-small Y-is-set = X/≈⁻ , ≃-sym e
  where
   open replacement-construction f Y-is-loc-small Y-is-set
   e = image f ≃⟨ image-≃-quotient ⟩
       X/≈     ≃⟨ X/≈-≃-X/≈⁻       ⟩
       X/≈⁻    ■


\end{code}
