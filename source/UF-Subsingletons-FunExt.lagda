In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-LeftCancellable

is-prop-exponential-ideal : ∀ {U V} → funext U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → is-prop (A x)) → is-prop (Π A) 
is-prop-exponential-ideal fe {X} {A} isa f g = dfunext fe (λ x → isa x (f x) (g x))

is-prop-is-prop : ∀ {U} {X : U ̇} → funext U U → is-prop (is-prop X)
is-prop-is-prop {U} {X} fe f g = claim₁
 where
  lemma : is-set X
  lemma = prop-is-set f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x 
  claim₀ x = dfunext fe (claim x) 
  claim₁ : f ≡ g
  claim₁  = dfunext fe claim₀

is-prop-is-singleton : ∀ {U} {X : U ̇} → funext U U → is-prop(is-singleton X)
is-prop-is-singleton {U} {X} fe (x , φ) (y , γ) = to-Σ-≡'' (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : is-prop X
  isp = is-singleton-is-prop (y , γ)
  iss : is-set X
  iss = prop-is-set isp

is-set-exponential-ideal : ∀ {U V} → funext U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → is-set(A x)) → is-set(Π A) 
is-set-exponential-ideal {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)
  b : is-prop(f ≡ g)
  b = left-cancellable-reflects-is-prop happly (section-lc happly (pr₂ (fe f g))) a


\end{code}

The following code is used to make Agda work with the constructions we
have given. We make the implicit arguments explicit in the definition
of is-set.

\begin{code}

is-set' : ∀ {U} → U ̇ → U ̇
is-set' X = (x y : X) → is-prop(x ≡ y)

is-set'-is-set : ∀ {U} {X : U ̇} → is-set' X → is-set X
is-set'-is-set s {x} {y} = s x y

is-set-is-set' : ∀ {U} {X : U ̇} → is-set X → is-set' X
is-set-is-set' s x y = s {x} {y}

is-prop-is-set' : ∀ {U} {X : U ̇} → funext U U → is-prop (is-set' X)
is-prop-is-set' fe = is-prop-exponential-ideal fe
                       (λ x → is-prop-exponential-ideal fe
                       (λ y → is-prop-is-prop fe))

is-prop-is-set : ∀ {U} {X : U ̇} → funext U U → is-prop (is-set X)
is-prop-is-set {U} {X} fe = g
 where
  g : is-prop (is-set X)
  g = subtype-of-prop-is-prop is-set-is-set' (λ p → ap is-set'-is-set p) (is-prop-is-set' fe)

\end{code}

\begin{code}

decidable-is-prop : ∀ {U} {P : U ̇} → funext U U₀ → is-prop P → is-prop(P + ¬ P)
decidable-is-prop fe₀ isp = sum-of-contradictory-props
                             isp
                             (is-prop-exponential-ideal fe₀ λ _ → 𝟘-is-prop)
                             (λ p u → u p)

PropExt : ∀ {U} → funext U U → propext U → {p q : Ω {U}}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
        to-Σ-≡'' ((pe (holds-is-prop p) (holds-is-prop q) f g) , is-prop-is-prop fe _ _)

Ω-is-set : ∀ {U} → funext U U → propext U → is-set (Ω {U})
Ω-is-set {U} fe pe = identification-collapsible-is-set pc
 where
  A : (p q : Ω) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds) 
  A-is-prop : (p q : Ω) → is-prop(A p q)
  A-is-prop p q = is-prop-closed-under-Σ (is-prop-exponential-ideal fe (λ _ → holds-is-prop q)) 
                                       (λ _ → is-prop-exponential-ideal fe (λ _ → holds-is-prop p)) 
  g : (p q : Ω) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Ω) → A p q → p ≡ q 
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Ω) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Ω) (d e : p ≡ q) → f p q d ≡ f p q e 
  constant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))
  pc : {p q : Ω} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

neg-is-prop : ∀ {U} {X : U ̇} → funext U U₀ → is-prop(¬ X)
neg-is-prop fe u v = dfunext fe (λ x → 𝟘-elim (u x)) 

\end{code}

For the moment we work with U₀ here because 𝟙 and ⊤ live in U₀:

\begin{code}

equal-⊤-is-true : (P : U₀ ̇) (hp : is-prop P)
               → (P , hp) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

true-is-equal-⊤ : propext U₀ → funext U₀ U₀ → (P : U₀ ̇) (hp : is-prop P)
                → P → (P , hp) ≡ ⊤
true-is-equal-⊤ pe fe P hp x = to-Σ-≡ P 𝟙 hp 𝟙-is-prop (pe hp 𝟙-is-prop unique-to-𝟙 λ _ → x)
                                                        (is-prop-is-prop fe _ _)

Ω-ext : propext U₀ → funext U₀ U₀ → {p q : Ω}
      → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q
Ω-ext pe fe {(P , isp)} {(Q , isq)} f g = to-Σ-≡ P Q isp isq (pe isp isq I II) (is-prop-is-prop fe _ _ ) 
 where
  I : P → Q
  I x = equal-⊤-is-true Q isq (f (true-is-equal-⊤ pe fe P isp x))
  II : Q → P
  II y = equal-⊤-is-true P isp (g (true-is-equal-⊤ pe fe Q isq y))

\end{code}
