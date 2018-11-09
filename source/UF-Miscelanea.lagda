Martin Escardo

UF things that depend on non-UF things.

\begin{code}

module UF-Miscelanea where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Retracts

decidable-is-collapsible : {X : U ̇} → decidable X → collapsible X
decidable-is-collapsible (inl x) = pointed-types-are-collapsible x
decidable-is-collapsible (inr u) = empty-types-are-collapsible u

open import DiscreteAndSeparated

discrete-is-Id-collapsible : {X : U ̇} → discrete X → Id-collapsible X
discrete-is-Id-collapsible d = decidable-is-collapsible (d _ _)

discrete-is-set : {X : U ̇} → discrete X → is-set X
discrete-is-set d = Id-collapsibles-are-sets(discrete-is-Id-collapsible d)

isolated-is-h-isolated : {X : U ̇} (x : X) → isolated x → is-h-isolated x
isolated-is-h-isolated {U} {X} x i {y} = local-hedberg x (λ y → γ y (i y)) y
 where
  γ : (y : X) → decidable (x ≡ y) → Σ \(f : x ≡ y → x ≡ y) → constant f
  γ y (inl p) = (λ _ → p) , (λ q r → refl)
  γ y (inr n) = id , (λ q r → 𝟘-elim (n r))

isolated-inl : {X : U ̇} (x : X) (i : isolated x) (y : X) (r : x ≡ y) → i y ≡ inl r
isolated-inl x i y r =
  equality-cases (i y)
    (λ (p : x ≡ y) (q : i y ≡ inl p) → q ∙ ap inl (isolated-is-h-isolated x i p r))
    (λ (h : ¬(x ≡ y)) (q : i y ≡ inr h) → 𝟘-elim(h r))

discrete-inl : {X : U ̇} (d : discrete X) (x y : X) (r : x ≡ y) → d x y ≡ inl r
discrete-inl d x y r =
  equality-cases (d x y)
    (λ (p : x ≡ y) (q : d x y ≡ inl p) → q ∙ ap inl (discrete-is-set d p r))
    (λ (h : ¬(x ≡ y)) (q : d x y ≡ inr h) → 𝟘-elim(h r))

discrete-inr : {X : U ̇} → funext U U₀
            → (d : discrete X) (x y : X) (n : ¬(x ≡ y)) → d x y ≡ inr n
discrete-inr fe d x y n =
  equality-cases (d x y)
    (λ (p : x ≡ y) (q : d x y ≡ inl p) → 𝟘-elim (n p))
    (λ (m : ¬(x ≡ y)) (q : d x y ≡ inr m) → q ∙ ap inr (nfunext fe (λ (p : x ≡ y) → 𝟘-elim (m p))))

isolated-Id-is-prop : {X : U ̇} (x : X) → isolated' x → (y : X) → is-prop (y ≡ x)
isolated-Id-is-prop x i = local-hedberg' x (λ y → decidable-is-collapsible (i y))

Σ-discrete : {X : U ̇} → {Y : X → V ̇}
          → discrete X → ((x : X) → discrete(Y x)) → discrete(Σ Y)
Σ-discrete {U} {V} {X} {Y} d e (x , y) (x' , y') = g (d x x')
 where
  g : decidable(x ≡ x') → decidable(x , y ≡ x' , y')
  g (inl p) = f (e x' (transport Y p y) y')
   where
    f : decidable(transport Y p y ≡ y') → decidable((x , y) ≡ (x' , y'))
    f (inl q) = inl (to-Σ-≡ (p , q))
    f (inr ψ) = inr c
     where
      c : x , y ≡ x' , y' → 𝟘
      c r = ψ q
       where
        p' : x ≡ x'
        p' = ap pr₁ r
        q' : transport Y p' y ≡ y'
        q' = from-Σ-≡' r
        s : p ≡ p'
        s = discrete-is-set d p p'
        q : transport Y p y ≡ y'
        q = ap (λ - → transport Y - y) s ∙ q'
  g (inr φ) = inr (λ q → φ (ap pr₁ q))

𝟚-is-set : is-set 𝟚
𝟚-is-set = discrete-is-set 𝟚-discrete

ℕ-is-set : is-set ℕ
ℕ-is-set = discrete-is-set ℕ-discrete

nonempty : U ̇ → U ̇
nonempty X = is-empty(is-empty X)

stable : U ̇ → U ̇
stable X = nonempty X → X

decidable-is-stable : {X : U ̇} → decidable X → stable X
decidable-is-stable (inl x) φ = x
decidable-is-stable (inr u) φ = unique-from-𝟘(φ u)

stable-is-collapsible : funext U U₀ → {X : U ̇} → stable X → collapsible X
stable-is-collapsible {U} fe {X} s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)
  claim₀ : (x y : X) → (u : is-empty X) → u x ≡ u y
  claim₀ x y u = unique-from-𝟘(u x)
  claim₁ : (x y : X) → (λ u → u x) ≡ (λ u → u y)
  claim₁ x y = dfunext fe (claim₀ x y)
  g : (x y : X) → f x ≡ f y
  g x y = ap s (claim₁ x y)

separated-is-Id-collapsible : funext U U₀ → {X : U ̇} → separated X → Id-collapsible X
separated-is-Id-collapsible fe s = stable-is-collapsible fe (s _ _)

separated-is-set : funext U U₀ → {X : U ̇} → separated X → is-set X
separated-is-set fe s = Id-collapsibles-are-sets (separated-is-Id-collapsible fe s)

is-prop-separated : funext U U → funext U U₀ → {X : U ̇} → is-prop(separated X)
is-prop-separated fe fe₀ {X} = iprops-are-propositions f
 where
  f : separated X → is-prop(separated X)
  f s = Π-is-prop fe
          (λ _ → Π-is-prop fe
                    (λ _ → Π-is-prop fe
                              (λ _ → separated-is-set fe₀ s)))

\end{code}

Find a better home for this:

\begin{code}

𝟚-ℕ-embedding : 𝟚 → ℕ
𝟚-ℕ-embedding ₀ = 0
𝟚-ℕ-embedding ₁ = 1

𝟚-ℕ-embedding-lc : left-cancellable 𝟚-ℕ-embedding
𝟚-ℕ-embedding-lc {₀} {₀} refl = refl
𝟚-ℕ-embedding-lc {₀} {₁} ()
𝟚-ℕ-embedding-lc {₁} {₀} ()
𝟚-ℕ-embedding-lc {₁} {₁} refl = refl

C-B-embedding : (ℕ → 𝟚) → (ℕ → ℕ)
C-B-embedding α = 𝟚-ℕ-embedding ∘ α

C-B-embedding-lc : funext U₀ U₀ → left-cancellable C-B-embedding
C-B-embedding-lc fe {α} {β} p = dfunext fe h
 where
  h : (n : ℕ) → α n ≡ β n
  h n = 𝟚-ℕ-embedding-lc (ap (λ - → - n) p)

\end{code}
