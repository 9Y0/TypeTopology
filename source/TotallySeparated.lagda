Martin Escardo 2011, 2017, 2018.

We define and study totally separated types. Most of the material in
this file is from January 2018.

The terminology "totally separated" comes from topology, where it
means that the clopens separate the points. Here the maps into 𝟚
separate the points, formulated in a positive way.

Any type has a totally separated reflection, assuming function
extensionality and propositional truncations.

All the simple types (those obtained from 𝟚 and ℕ by iterating
function spaces) are totally separated (see the module
SimpleTypes). This is because the totally separated types form an
exponential ideal. Moreover, Π Y is totally separated for any family
Y:X→U provided Y x is totally separated for all x:X. This assumes
function extensionality.

In particular, the Cantor and Baire types 𝟚^ℕ and ℕ^ℕ are totally
separated (like in topology).

Closure under Σ fails in general. However, ℕ∞ (defined with Σ) is
totally separated (proved in the module GenericConvergentSequence).

A counter-example to closure under Σ (from 2012) is in the file
http://www.cs.bham.ac.uk/~mhe/agda-new/FailureOfTotalSeparatedness.html

This is the "compactification" of ℕ with two points at infinity:

   Σ \(u : ℕ∞) → u ≡ ∞ → 𝟚.

If there is a 𝟚-valued function separating the two points at infinity,
then WLPO holds. (The totally separated reflection of this type should
be ℕ∞ if ¬WLPO holds.)

(In the context of topology, I learned this example from the late
Klaus Keimel (but the rendering in type theory is mine), where it is a
T₁, non-T₂, and non totally separated space which is zero dimensional
(has a base of clopen sets), and where the intersection of two compact
subsets need not be compact. The failure of the Hausdorff property is
with the two points an infinity, which can't be separated by disjoint
open neightbourhoods.)

The total separatedness of the reals (of any kind) should also give a
taboo. All non-sets fail (without the need of taboos) to be totally
separated, because totally separated spaces are sets.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module TotallySeparated where

open import UF
open import Two
open import DiscreteAndSeparated hiding (tight)

totally-separated : ∀ {U} → U ̇ → U ̇
totally-separated X = {x y : X} → ((p : X → 𝟚) → p x ≡ p y) → x ≡ y

\end{code}

Excluded middle implies that all sets are discrete and hence totally
separated:

\begin{code}

discrete-totally-separated : ∀ {U} {X : U ̇} → discrete X → totally-separated X
discrete-totally-separated {U} {X} d {x} {y} α = g
 where
  open import DecidableAndDetachable
  p : X → 𝟚
  p = pr₁ (characteristic-function (d x))
  
  φ : (y : X) → (p y ≡ ₀ → x ≡ y) × (p y ≡ ₁ → ¬ (x ≡ y))
  φ = pr₂ (characteristic-function (d x))
  
  b : p x ≡ ₀
  b = Lemma[b≢₁→b≡₀] (λ s → pr₂ (φ x) s refl)
  
  a : p y ≡ ₀
  a = (α p)⁻¹ ∙ b
  
  g : x ≡ y
  g = pr₁ (φ y) a

\end{code}

The converse fails: by the results below, e.g. (ℕ → 𝟚) is totally
separated, but its discreteness amounts to WLPO.

\begin{code}

retract-totally-separated : ∀ {U V} {X : U ̇} {Y : V ̇}
                         → retract Y of X → totally-separated X → totally-separated Y
retract-totally-separated (r , (s , rs)) ts {y} {y'} α = section-lc s (r , rs) h
 where
  h : s y ≡ s y'
  h = ts (λ p → α (p ∘ s))

totally-separated-is-separated : ∀ {U} (X : U ̇) → totally-separated X → separated X
totally-separated-is-separated X ts = g
 where
  g : (x y : X) → ¬¬(x ≡ y) → x ≡ y
  g x y φ  = ts h
   where
    a : (p : X → 𝟚) → ¬¬(p x ≡ p y)
    a p = ¬¬-functor (ap p {x} {y}) φ
    
    h : (p : X → 𝟚) → p x ≡ p y
    h p = 𝟚-separated (p x) (p y) (a p)

open import UF2

totally-separated-is-set : ∀ {U} → FunExt U U₀ → (X : U ̇) → totally-separated X → isSet X
totally-separated-is-set fe X t = separated-is-set fe (totally-separated-is-separated X t)

\end{code}

The converse fails: the type of propositions is a set, but its total
separatedness implies excluded middle. In fact, its separatedness
already implies excluded middle (exercise).

Old proof:

\begin{code}

totally-separated-is-set' : ∀ {U} → FunExt U U₀ → (X : U ̇) → totally-separated X → isSet X
totally-separated-is-set' fe X t = path-collapsible-is-set h
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f r = t(λ p → ap p r)
  
  b : {x y : X} (φ γ : (p : X → 𝟚) → p x ≡ p y) → φ ≡ γ
  b φ γ = funext fe (λ p → discrete-is-set 𝟚-discrete (φ p) (γ p))
  
  c : {x y : X} (r s : x ≡ y) → (λ p → ap p r) ≡ (λ p → ap p s)
  c r s = b(λ p → ap p r) (λ p → ap p s)
  
  g : {x y : X} → constant(f {x} {y})
  g r s = ap t (c r s)
  
  h : path-collapsible X
  h {x} {y} = f , g

\end{code}

We now characterize the totally separated types X as those such that
the map eval {X} is an embedding, in order to construct totally
separated reflections.

\begin{code}

𝟚-totally-separated : totally-separated 𝟚
𝟚-totally-separated e = e id

totally-separated-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {Y : X → V ̇}
                       → ((x : X) → totally-separated(Y x)) → totally-separated(Π Y)
totally-separated-ideal fe {X} {Y} t {f} {g} e = funext fe h
 where
   P : (x : X) (p : Y x → 𝟚) → Π Y → 𝟚
   P x p f = p(f x)
   
   h : (x : X) → f x ≡ g x
   h x = t x (λ p → e(P x p))

eval : ∀ {U} {X : U ̇} → X → ((X → 𝟚) → 𝟚)
eval x = λ p → p x

tsieeval : ∀ {U} {X : U ̇} → FunExt U U₀ → totally-separated X → isEmbedding(eval {U} {X})
tsieeval {U} {X} fe ts φ (x , p) (y , q) = to-Σ-Id _ (t , r)
  where
   s : eval x ≡ eval y
   s = p ∙ q ⁻¹
   
   t : x ≡ y
   t = ts (λ p → ap (λ φ → φ p) s)
   
   r : transport (λ x → eval x ≡ φ) t p ≡ q
   r = totally-separated-is-set fe
         ((X → 𝟚) → 𝟚) (totally-separated-ideal fe (λ p → 𝟚-totally-separated)) _ q

ieevalts : ∀ {U} {X : U ̇} → FunExt U U₀ → isEmbedding(eval {U} {X}) → totally-separated X
ieevalts {U} {X} fe i {x} {y} e = ap pr₁ q
  where
   φ : (X → 𝟚) → 𝟚
   φ = eval x
   
   h : isProp (fiber eval  φ)
   h = i φ
   
   g : eval y ≡ φ
   g = funext fe (λ p → (e p)⁻¹)
   
   q : x , refl ≡ y , g
   q = h (x , refl) (y , g)

\end{code}

 Now, if a type is not (necessarily) totally separated, we can
 consider the image of the map eval {X}, and this gives the totally
 separated reflection, with the corestriction of eval {X} to its image
 as its reflector.

\begin{code}

module TotallySeparatedReflection
         {U  : Universe}
         (fe : ∀ U V → FunExt U V)
         (pt : PropTrunc)
 where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

 T : U ̇ → U ̇
 T X = image (eval {U} {X})
 
 tts : {X : U ̇} → totally-separated(T X)
 tts {X} {φ , s} {γ , t} = g
  where
   f : (e : (q : T X → 𝟚) → q (φ , s) ≡ q (γ , t)) (p : X → 𝟚) → φ p ≡ γ p
   f e p = e (λ (x' : T X) → pr₁ x' p)

   g : (e : (q : T X → 𝟚) → q (φ , s) ≡ q (γ , t)) → (φ , s) ≡ (γ , t)
   g e = to-Σ-Id _ (funext (fe U U₀) (f e), ptisp _ t)

 η : {X : U ̇} → X → T X
 η {X} = corestriction (eval {U} {X})

 η-surjection : {X : U ̇} → isSurjection(η {X})
 η-surjection = corestriction-surjection eval

 η-induction : ∀ {W} {X : U ̇} (P : T X → W ̇)
             → ((x' : T X) → isProp(P x'))
             → ((x : X) → P(η x))
             → (x' : T X) → P x'
 η-induction = surjection-induction η η-surjection

 totally-separated-reflection : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                              → (f : X → A) → isContr (Σ \(f' : T X → A) → f' ∘ η ≡ f)
 totally-separated-reflection {V} {X} {A} ts f = go
  where
   ie : (γ : (A → 𝟚) → 𝟚) → isProp (Σ \(a : A) → eval a ≡ γ)
   ie = tsieeval (fe V U₀) ts
   
   h : (φ : (X → 𝟚) → 𝟚) → (∃ \(x : X) → eval x ≡ φ) → Σ \(a : A) → eval a ≡ (λ q → φ(q ∘ f))
   h φ = ptrec (ie γ) u
    where
     γ : (A → 𝟚) → 𝟚
     γ q = φ (q ∘ f)
     
     u : (Σ \(x : X) → (λ p → p x) ≡ φ) → Σ \(a : A) → eval a ≡ γ
     u (x , r) = f x , funext (fe V U₀) (λ q → ap (λ φ → φ (q ∘ f)) r)
     
   h' : (x' : T X) → Σ \(a : A) → eval a ≡ (λ q → pr₁ x' (q ∘ f))
   h' (φ , s) = h φ s
   
   f' : T X → A
   f' (φ , s) = pr₁ (h φ s)
   
   b : (x' : T X) (q : A → 𝟚) → q(f' x') ≡ pr₁ x' (q ∘ f)
   b (φ , s) q = ap (λ γ → γ q) (pr₂ (h φ s))
   
   r : f' ∘ η ≡ f
   r = funext (fe U V) (λ x → ts (b (η x)))
   
   c : (σ : Σ \(f'' : T X → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-Id _ (funext (fe U V) t , v)
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w x = ap (λ f → f x) (r ∙ s ⁻¹)
     
     t : ∀ x' → f' x' ≡ f'' x'
     t = η-induction (λ x' → f' x' ≡ f'' x') (λ y' → totally-separated-is-set (fe V U₀) A ts) w
     
     u : f'' ∘ η ≡ f
     u = transport (λ g → g ∘ η ≡ f) (funext (fe U V) t) r
     
     v : u ≡ s
     v = totally-separated-is-set (fe (U ⊔ V) U₀) (X → A) (totally-separated-ideal (fe U V) (λ x → ts)) u s

   go : isContr (Σ \(f' : T X → A) → f' ∘ η ≡ f)
   go = (f' , r) , c

 totally-separated-reflection' : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                              → is-equiv (λ (f' : T X → A) → f' ∘ η)
 totally-separated-reflection' ts = isContrMap-is-equiv _ (totally-separated-reflection ts)

 totally-separated-reflection'' : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                               → (T X → A) ≃ (X → A)
 totally-separated-reflection'' ts = (λ f' → f' ∘ η) , totally-separated-reflection' ts

\end{code}

In particular, because 𝟚 is totally separated, T X and X have the same
boolean predicates (which we exploit in the module 2CompactTypes).


TODO: most of what we said doesn't depend on the type 𝟚, and total
separatedness can be generalized to S-separatedness for an arbitrary
type S, where 𝟚-separatedness is total separatedness. Then, for
example, Prop-separated is equivalent to is-set, all types in U are U
separated, Set-separatedness (where Set is the type of sets) should be
equivalent to is-1-groupoid, etc.

An interesting case is when S is (the total space of) a dominance,
generalizing the case S=Prop. Because the partial elements are defined
in terms of maps into S, the S-lifting of a type X should coincide
with the S-separated reflection of the lifting of X, and hence, in
this context, it makes sense to restrict our attention to S-separated
types.

Another useful thing is that in a totally separated type X we can
define a tight apartness relation x♯y by ∃(p:X→𝟚), p(x)‌≠p(y), where
tightness means ¬(x♯y)→x=y. Part of the following should be moved to
another module about apartness, but I keep it here for the moment.

26 January 2018.

\begin{code}

module Apartness (pt : PropTrunc) where

 open PropositionalTruncation (pt)

 prop-valued : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 prop-valued _♯_ = ∀ x y → isProp(x ♯ y)

 irreflexive : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 irreflexive _♯_ = ∀ x → ¬(x ♯ x)

 symmetric : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 symmetric _♯_ = ∀ x y → x ♯ y → y ♯ x

 cotransitive : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 cotransitive _♯_ = ∀ x y z → x ♯ y → x ♯ z ∨ y ♯ z

 tight : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 tight _♯_ = ∀ x y → ¬(x ♯ y) → x ≡ y

 apartness : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 apartness _♯_ = prop-valued _♯_ × irreflexive _♯_ × symmetric _♯_ × cotransitive _♯_

\end{code}

TODO. Clearly, all of the above are proposition-valued.

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{code}

 _♯₂_ : ∀ {U} {X : U ̇} → X → X → U ̇
 x ♯₂ y = ∃ \(p : _ → 𝟚) → p x ≢ p y

 ♯₂-is-apartness : ∀ {U} {X : U ̇} → apartness (_♯₂_ {U} {X})
 ♯₂-is-apartness {U} {X} = a , b , c , d
  where
   a : prop-valued _♯₂_
   a x y = ptisp

   b : irreflexive _♯₂_
   b x = ptrec 𝟘-isProp g
    where
     g : ¬ Σ \(p : X → 𝟚) → p x ≢ p x
     g (p , u) = u refl
     
   c : symmetric _♯₂_
   c x y = ptfunct g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → Σ \(p : _ → 𝟚) → p y ≢ p x
     g (p , u) = p , ≢-sym u
   
   d : cotransitive _♯₂_
   d x y z = ptfunct g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
     g (p , u) = h (discrete-is-cotransitive 𝟚-discrete {p x} {p y} {p z} u)
      where
       h : (p x ≢ p z) + (p z ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
       h (inl u) = inl ∣ p , u ∣
       h (inr v) = inr ∣ p , ≢-sym v ∣

 ♯₂-tight-ts : ∀ {U} {X : U ̇} → tight (_♯₂_ {U} {X}) → totally-separated X
 ♯₂-tight-ts {U} {X} t {x} {y} α = t x y (ptrec 𝟘-isProp h)
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = u (α p)

 ts-♯₂-tight : ∀ {U} {X : U ̇} → totally-separated X → tight (_♯₂_ {U} {X})
 ts-♯₂-tight {U} {X} ts x y na = ts α
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = na ∣ p , u ∣

   α : (p : X → 𝟚) → p x ≡ p y
   α p = 𝟚-separated (p x) (p y) (λ u → h (p , u))

\end{code}
