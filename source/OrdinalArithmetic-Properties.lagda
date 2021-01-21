Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module OrdinalArithmetic-Properties
       (ua : Univalence)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt
open import UF-EquivalenceExamples

private
 fe : FunExt
 fe = FunExt-from-Univalence ua

open import SpartanMLTT
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalArithmetic fe

𝟘ₒ-left-neutral : (α : Ordinal 𝓤) → 𝟘ₒ +ₒ α ≡ α
𝟘ₒ-left-neutral α = eqtoidₒ (𝟘ₒ +ₒ α) α h
 where
  f : 𝟘 + ⟨ α ⟩ → ⟨ α ⟩
  f = ⌜ 𝟘-lneutral ⌝

  f-preserves-order : (x y : 𝟘 + ⟨ α ⟩) → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y → f x ≺⟨ α ⟩ f y
  f-preserves-order (inr x) (inr y) l = l

  f-reflects-order : (x y : 𝟘 + ⟨ α ⟩) → f x ≺⟨ α ⟩ f y → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y
  f-reflects-order (inr x) (inr y) l = l


  h : (𝟘ₒ +ₒ α) ≃ₒ α
  h = f , order-equiv-criterion (𝟘ₒ +ₒ α) α f
           (⌜⌝-is-equiv 𝟘-lneutral) f-preserves-order f-reflects-order

𝟘ₒ-right-neutral : (α : Ordinal 𝓤) → α  +ₒ 𝟘ₒ ≡ α
𝟘ₒ-right-neutral α = eqtoidₒ (α +ₒ 𝟘ₒ) α h
 where
  f : ⟨ α ⟩ + 𝟘 → ⟨ α ⟩
  f = ⌜ 𝟘-rneutral' ⌝

  f-preserves-order : is-order-preserving (α  +ₒ 𝟘ₒ) α f
  f-preserves-order (inl x) (inl y) l = l

  f-reflects-order : is-order-reflecting (α  +ₒ 𝟘ₒ) α f
  f-reflects-order (inl x) (inl y) l = l


  h : (α +ₒ 𝟘ₒ) ≃ₒ α
  h = f , order-equiv-criterion (α +ₒ 𝟘ₒ) α f
           (⌜⌝-is-equiv 𝟘-rneutral') f-preserves-order f-reflects-order

+ₒ-assoc : (α β γ : Ordinal 𝓤) → (α  +ₒ β) +ₒ γ ≡ α  +ₒ (β +ₒ γ)
+ₒ-assoc α β γ = eqtoidₒ ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) h
 where
  f : ⟨ (α +ₒ β) +ₒ γ ⟩ → ⟨ α +ₒ (β +ₒ γ) ⟩
  f = ⌜ +assoc ⌝

  f-preserves-order : is-order-preserving  ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-preserves-order (inl (inl x)) (inl (inl y)) l = l
  f-preserves-order (inl (inl x)) (inl (inr y)) l = l
  f-preserves-order (inl (inr x)) (inl (inr y)) l = l
  f-preserves-order (inl (inl x)) (inr y)       l = l
  f-preserves-order (inl (inr x)) (inr y)       l = l
  f-preserves-order (inr x)       (inr y)       l = l


  f-reflects-order : is-order-reflecting ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-reflects-order (inl (inl x)) (inl (inl y)) l = l
  f-reflects-order (inl (inl x)) (inl (inr y)) l = l
  f-reflects-order (inl (inr x)) (inl (inr y)) l = l
  f-reflects-order (inl (inl x)) (inr y)       l = l
  f-reflects-order (inl (inr x)) (inr y)       l = l
  f-reflects-order (inr x)       (inl (inl y)) l = l
  f-reflects-order (inr x)       (inl (inr y)) l = l
  f-reflects-order (inr x)       (inr y)       l = l


  h : ((α  +ₒ β) +ₒ γ) ≃ₒ (α  +ₒ (β +ₒ γ))
  h = f , order-equiv-criterion ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
           (⌜⌝-is-equiv +assoc) f-preserves-order f-reflects-order

+ₒ-↓-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ≡ ((α +ₒ β) ↓ inl a)
+ₒ-↓-left {𝓤} {α} {β} a = h
 where
  γ = α ↓ a
  δ = (α  +ₒ β) ↓ inl a

  f : ⟨ γ ⟩ → ⟨ δ ⟩
  f (x , l) = inl x , l

  g :  ⟨ δ ⟩ → ⟨ γ ⟩
  g (inl x , l) = x , l

  η : g ∘ f ∼ id
  η u = refl

  ε : f ∘ g ∼ id
  ε (inl x , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)

  f-is-order-preserving : is-order-preserving γ δ f
  f-is-order-preserving (x , _) (x' , _) l = l


  g-is-order-preserving : is-order-preserving δ γ g
  g-is-order-preserving (inl x , _) (inl x' , _) l = l

  h : γ ≡ δ
  h = eqtoidₒ γ δ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)


+ₒ-↓-right : {α β : Ordinal 𝓤} (b : ⟨ β ⟩)
           → (α +ₒ (β ↓ b)) ≡ ((α +ₒ β) ↓ inr b)
+ₒ-↓-right {𝓤} {α} {β} b = h
 where
  γ = α  +ₒ (β ↓ b)
  δ = (α  +ₒ β) ↓ inr b

  f : ⟨ γ ⟩ → ⟨ δ ⟩
  f (inl a)       = inl a , *
  f (inr (y , l)) = inr y , l

  g :  ⟨ δ ⟩ → ⟨ γ ⟩
  g (inl a , *) = inl a
  g (inr y , l) = inr (y , l)

  η : g ∘ f ∼ id
  η (inl a)       = refl
  η (inr (y , l)) = refl

  ε : f ∘ g ∼ id
  ε (inl a , *) = refl
  ε (inr y , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)

  f-is-order-preserving : is-order-preserving γ δ f
  f-is-order-preserving (inl _) (inl _) l = l
  f-is-order-preserving (inl _) (inr _) l = l
  f-is-order-preserving (inr _) (inr _) l = l

  g-is-order-preserving : is-order-preserving δ γ g
  g-is-order-preserving (inl _ , _) (inl _ , _) l = l
  g-is-order-preserving (inl _ , _) (inr _ , _) l = l
  g-is-order-preserving (inr _ , _) (inr _ , _) l = l

  h : γ ≡ δ
  h = eqtoidₒ γ δ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

+ₒ-⊲-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ⊲ (α +ₒ β)
+ₒ-⊲-left {𝓤} {α} {β} a = inl a , +ₒ-↓-left a

+ₒ-⊲-right : {α β : Ordinal 𝓤} (b : ⟨ β ⟩)
           → (α +ₒ (β ↓ b)) ⊲ (α +ₒ β)
+ₒ-⊲-right {𝓤} {α} {β} b = inr b , +ₒ-↓-right {𝓤} {α} {β} b

+ₒ-increasing-on-right : {α β γ : Ordinal 𝓤}
                       → β ⊲ γ
                       → (α +ₒ β) ⊲ (α +ₒ γ)
+ₒ-increasing-on-right {𝓤} {α} {β} {γ} (c , p) = inr c , q
 where
  q =  (α +ₒ β)           ≡⟨ ap (α +ₒ_) p ⟩
       (α +ₒ (γ ↓ c))     ≡⟨ +ₒ-↓-right c ⟩
       ((α +ₒ γ) ↓ inr c) ∎

+ₒ-right-monotone : (α β γ : Ordinal 𝓤)
                  → β ≼ γ
                  → (α +ₒ β) ≼ (α +ₒ γ)
+ₒ-right-monotone α β γ m = to-≼ ϕ
 where
  l : (a : ⟨ α ⟩) → ((α +ₒ β) ↓ inl a) ⊲  (α +ₒ γ)
  l a = o
   where
    n : (α  ↓ a) ⊲ (α +ₒ γ)
    n = +ₒ-⊲-left a

    o : ((α +ₒ β) ↓ inl a) ⊲  (α +ₒ γ)
    o = transport (_⊲ (α +ₒ γ)) (+ₒ-↓-left a) n

  r : (b : ⟨ β ⟩) → ((α +ₒ β) ↓ inr b) ⊲ (α +ₒ γ)
  r b = s
   where
    o : (β ↓ b) ⊲ γ
    o = from-≼ m b

    p : (α +ₒ (β ↓ b)) ⊲ (α +ₒ γ)
    p = +ₒ-increasing-on-right o

    q : α +ₒ (β ↓ b) ≡ (α +ₒ β) ↓ inr b
    q = +ₒ-↓-right b

    s : ((α +ₒ β) ↓ inr b) ⊲ (α +ₒ γ)
    s = transport (_⊲ (α  +ₒ γ)) q p

  ϕ : (x : ⟨ α +ₒ β ⟩) → ((α +ₒ β) ↓ x) ⊲ (α +ₒ γ)
  ϕ = dep-cases l r


\end{code}

TODO. Find better names for the following lemmas.

\begin{code}

lemma₀ : {α β : Ordinal 𝓤}
       → α ≼ (α +ₒ β)
lemma₀ {𝓤} {α} {β} = to-≼ ϕ
 where
  ϕ : (a : ⟨ α ⟩) → Σ z ꞉ ⟨ α +ₒ β ⟩ , (α ↓ a) ≡ ((α +ₒ β) ↓ z)
  ϕ a = inl a , (+ₒ-↓-left a)

lemma₁ : {α β : Ordinal 𝓤}
         (a : ⟨ α ⟩)
       → (α +ₒ β) ≢ (α ↓ a)
lemma₁ {𝓤} {α} {β} a p = irrefl (O 𝓤) (α +ₒ β) m
 where
  l : (α +ₒ β) ⊲ α
  l = (a , p)

  m : (α +ₒ β) ⊲ (α +ₒ β)
  m = lemma₀ (α +ₒ β) l

lemma₂ : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
       → α ≡ β
       → Σ b ꞉ ⟨ β ⟩ , (α ↓ a) ≡ (β ↓ b)
lemma₂ a refl = a , refl

lemma₃ : {α β γ : Ordinal 𝓤} (b : ⟨ β ⟩) (z : ⟨ α +ₒ γ ⟩)
       → ((α +ₒ β) ↓ inr b) ≡ ((α +ₒ γ) ↓ z)
       → Σ c ꞉ ⟨ γ ⟩ , z ≡ inr c
lemma₃ {𝓤} {α} {β} {γ} b (inl a) p = 𝟘-elim (lemma₁ a q)
 where
  q : (α +ₒ (β ↓ b)) ≡ (α ↓ a)
  q = +ₒ-↓-right b ∙ p ∙ (+ₒ-↓-left a)⁻¹

lemma₃ b (inr c) p = c , refl

+ₒ-left-cancellable : (α β γ : Ordinal 𝓤)
                    → (α +ₒ β) ≡ (α +ₒ γ)
                    → β ≡ γ
+ₒ-left-cancellable {𝓤} α = g
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β = ∀ γ → (α +ₒ β) ≡ (α +ₒ γ) → β ≡ γ

  ϕ : ∀ β
    → (∀ b → P (β ↓ b))
    → P β
  ϕ β f γ p = Extensionality (O 𝓤) β γ (to-≼ u) (to-≼ v)
   where
    u : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
    u b = c , t
     where
      z : ⟨ α +ₒ γ ⟩
      z = pr₁ (lemma₂ (inr b) p)

      r : ((α +ₒ β) ↓ inr b) ≡ ((α +ₒ γ) ↓ z)
      r = pr₂ (lemma₂ (inr b) p)

      c : ⟨ γ ⟩
      c = pr₁ (lemma₃ b z r)

      s : z ≡ inr c
      s = pr₂ (lemma₃ b z r)

      q = (α +ₒ (β ↓ b))     ≡⟨ +ₒ-↓-right b ⟩
          ((α +ₒ β) ↓ inr b) ≡⟨ r ⟩
          ((α +ₒ γ) ↓ z)     ≡⟨ ap ((α +ₒ γ) ↓_) s ⟩
          ((α +ₒ γ) ↓ inr c) ≡⟨ (+ₒ-↓-right c)⁻¹ ⟩
          (α +ₒ (γ ↓ c))     ∎

      t : (β ↓ b) ≡ (γ ↓ c)
      t = f b (γ ↓ c) q

    v : (c : ⟨ γ ⟩) → (γ ↓ c) ⊲ β
    v c = b , (t ⁻¹)
     where
      z : ⟨ α +ₒ β ⟩
      z = pr₁ (lemma₂ (inr c) (p ⁻¹))

      r : ((α +ₒ γ) ↓ inr c) ≡ ((α +ₒ β) ↓ z)
      r = pr₂ (lemma₂ (inr c) (p ⁻¹))

      b : ⟨ β ⟩
      b = pr₁ (lemma₃ c z r)

      s : z ≡ inr b
      s = pr₂ (lemma₃ c z r)

      q = (α +ₒ (γ ↓ c))     ≡⟨ +ₒ-↓-right c ⟩
          ((α +ₒ γ) ↓ inr c) ≡⟨ r ⟩
          ((α +ₒ β) ↓ z)     ≡⟨ ap ((α +ₒ β) ↓_) s ⟩
          ((α +ₒ β) ↓ inr b) ≡⟨ (+ₒ-↓-right b)⁻¹ ⟩
          (α +ₒ (β ↓ b))     ∎

      t : (β ↓ b) ≡ (γ ↓ c)
      t = f b (γ ↓ c) (q ⁻¹)

  g : (β : Ordinal 𝓤) → P β
  g = transfinite-induction-on-O P ϕ

\end{code}

This implies that the function α +ₒ_ reflects the _⊲_ ordering:

\begin{code}

+ₒ-left-reflects-⊲ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ⊲ (α +ₒ γ)
                   → β ⊲ γ
+ₒ-left-reflects-⊲ α β γ (inl a , p) = 𝟘-elim (lemma₁ a q)
   where
    q : (α +ₒ β) ≡ (α ↓ a)
    q = p ∙ (+ₒ-↓-left a)⁻¹

+ₒ-left-reflects-⊲ α β γ (inr c , p) = l
   where
    q : (α +ₒ β) ≡ (α +ₒ (γ ↓ c))
    q = p ∙ (+ₒ-↓-right c)⁻¹

    r : β ≡ (γ ↓ c)
    r = +ₒ-left-cancellable α β (γ ↓ c) q

    l : β ⊲ γ
    l = c , r

\end{code}

And in turn this implies that the function α +ₒ_ reflects the _≼_
partial ordering:

\begin{code}

+ₒ-left-reflects-≼ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ≼ (α +ₒ γ)
                   → β ≼ γ
+ₒ-left-reflects-≼ {𝓤} α β γ l = to-≼ (ϕ β l)
 where
  ϕ : (β : Ordinal 𝓤)
    → (α +ₒ β) ≼ (α +ₒ γ)
    → (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
  ϕ β l b = o
   where
    m : (α +ₒ (β ↓ b)) ⊲ (α +ₒ β)
    m = +ₒ-⊲-right b

    n : (α +ₒ (β ↓ b)) ⊲ (α +ₒ γ)
    n = l (α +ₒ (β ↓ b)) m

    o : (β ↓ b) ⊲ γ
    o = +ₒ-left-reflects-⊲ α (β ↓ b) γ n

\end{code}
