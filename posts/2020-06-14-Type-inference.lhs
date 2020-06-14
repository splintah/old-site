---
title: Type inference
series: "Introduction to Type Systems"
---

In the previous post, we have added polymorphism to the simply typed lambda calculus and implemented a type checker for the polymorphic lambda calculus.
In this post, we'll explore *type inference* or *reconstruction*.

<details>
<summary>Imports etc.</summary>

> module Inference where
>
> import           Control.Monad        (when)
> import           Control.Monad.Except
> import           Control.Monad.RWS
> import           Data.Bifunctor
> import qualified Data.Map.Strict      as Map
> import           Data.Map.Strict      (Map)
> import qualified Data.Set             as Set
> import           Data.Set             (Set)
> import           Test.QuickCheck

</details>

Motivation
==========

In the polymorphic lambda calculus, we can write polymorphic (generic) functions that work on all types, using *parametric polymorphic*.
This is a major benefit over the simply typed lambda calculus, because it reduces duplication: for example, we no longer have to write an identity function for every type that we might need one for, but can write exactly one identity function that works on all types.

But, as you might have noticed, it is quite some work to use such polymorphic functions.
Where we could define $\mathsf{const}$ as $\lambda x. \lambda y. x$ and use it like $\mathsf{const}\ (\lambda x. x)\ (\lambda f. \lambda x. f\ x)$ in the untyped lambda calculus, in the polymorphic lambda calculus we have to type $\mathsf{const} = \Lambda X. \Lambda Y. \lambda x : X. \lambda y : Y. x$ and use it like the following for the same example:
$$
\begin{align*}
  \mathsf{const}\ & (\forall X. X \rightarrow X) \\
    & (\forall A. \forall B. (A \rightarrow B) \rightarrow A \rightarrow B) \\
    & (\Lambda X. \lambda x : X. x) \\
    & (\Lambda A. \Lambda B. \lambda f : A \rightarrow B. \lambda x : A. f\ x)
\end{align*}
$$

We have to do a whole lot of typing to make the type checker happy.
Wouldn't it be nice if we could write our terms like in the untyped lambda calculus, with the same static safety as in the polymorphic lambda calculus?
It turns out that we can actually implement a type checker that *infers* or *reconstructs* the types from a fully untyped program.
This technique is called *type inference* or *type reconstruction*, and the corresponding type system is called the *Hindley-Milner type system*.

Syntax
======

To write programs without any type information, we remove all types from the syntax of terms.
So no more type abstractions, type applications or lambda abstractions with explicit types (e.g., we'll write $\lambda x. x$ instead of $\lambda x : X. x$).

The AST looks like this:

> data Term
>   = TmTrue
>     -- ^ True value
>   | TmFalse
>     -- ^ False value
>   | TmInt Integer
>     -- ^ Integer value
>   | TmVar String
>     -- ^ Variable
>   | TmAbs String Term
>     -- ^ Lambda abstraction
>   | TmApp Term Term
>     -- ^ Application
>   | TmAdd Term Term
>     -- ^ Addition
>   | TmIf Term Term Term
>     -- ^ If-then-else conditional
>   | TmLet String Term Term
>     -- ^ Let-in
>   deriving (Show, Eq)

You might notice that this is just the syntax of the untyped lambda calculus (`TmVar`, `TmAbs`, `TmApp`) with the syntax constructs of the simply typed lambda calculus (`TmTrue`, `TmFalse`, `TmInt`, `TmAdd`, `TmIf`), plus the addition of the `TmLet` constructor, which is used for terms of the form $\mathbf{let}\ x = t\ \mathbf{in}\ t'$.
The addition of let-in terms is not strictly necessary, but it is if we actually want to use polymorphism.
(This will be discussed later.)

For the syntax of types, we do have to make a substantial change, though.
We must restrict our usage of polymorphism: we can only use $\forall$'s at the top level; no more $(\forall A. A \rightarrow A) \rightarrow (\forall B. B \rightarrow B)$, for example.
We have to do this, because type inference for the polymorphic lambda calculus as we saw it in the previous post is [undecidable](https://en.wikipedia.org/wiki/Undecidable_problem).
We will therefore split our type syntax into two: *monotypes* and *polytypes* (or *type schemes*).

The syntax for *polytypes* (for which we'll write $\sigma$) is very simple:

$$
\begin{align*}
  \sigma ::=\ & \forall \vec{X}. \tau & \text{(polytype)} \\
\end{align*}
$$

Here $\tau$ is a monotype, and $\vec{X}$ is a (possibly empty) list of type variables.

In Haskell, this is:

> data Polytype
>   = TyForall [String] Type
>   deriving (Show, Eq)

(We'll use just `Type` to refer to monotypes.)

The syntax for monotypes looks like this:

$$
\begin{align*}
  \tau ::=\ & X & \text{(type variable)} \\
      \mid\ & \tau \rightarrow \tau' & \text{(function type)} \\
      \mid\ & \mathsf{Bool} & \text{(boolean type)} \\
      \mid\ & \mathsf{Int} & \text{(integer type)}
\end{align*}
$$

Or in Haskell:

> data Type
>   = TyVar String
>     -- ^ Type variable
>   | TyFun Type Type
>     -- ^ Function type
>   | TyBool
>     -- ^ Boolean type
>   | TyInt
>     -- ^ Integer type
>   deriving (Show, Eq)

The type for the identity function (which we now write as just $\lambda x. x$), $\forall X. X \rightarrow X$, is written in Haskell as:

> tmId :: Term
> tmId = TmAbs "x" (TmVar "x")
>
> tyId :: Polytype
> tyId = TyForall ["X"] $ TyFun (TyVar "X") (TyVar "X")

And $\mathsf{const}$:

> tmConst :: Term
> tmConst = TmAbs "a" (TmAbs "b" (TmVar "a"))
>
> tyConst :: Polytype
> tyConst = TyForall ["A", "B"] $ TyFun (TyVar "A") (TyFun (TyVar "B") (TyVar "A"))

Type checking
=============

Type inference is quite a bit harder than type checking the simply typed lambda calculus or the polymorphic lambda calculus *with* explicit type annotations.
We will use a constraint-based type inference algorithm, based on [*Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/), Benjamin C. Pierce, Chapter 22.3.
I have found this to be the most intuitive approach.
I will deviate a bit from Pierce's approach, though, to make the rules somewhat easier to read.[^deviation]

[^deviation]:
  Pierce uses the typing relation $\Gamma \vdash t : \tau \mid_X C$, where the set $X$ keeps track of the used type variables.
  This is very useful to formally reason about the type inference algorithm, but it makes the typing rules more complex than necessary for a Haskell implementation.
  Instead, I will just write $X \text{ fresh}$ for a type variable $X$.
  This approach is more informal, since it doesn't formally specify when a variable is *fresh*, but I think it is easier.

For type inference, we will use a different typing relation than the one we used for the simply typed and the polymorphic (but explicitly typed) lambda calculus.
Before, we used the relation $\Gamma \vdash t : \tau$, which could be read something like: *$\Gamma$ entails that $t$ has type $\tau$*.
Now, we will use the typing relation written as follows: $\Gamma \vdash t : \tau \mid C$.
This can be read as: *$\Gamma$ entails that $t$ has type $\tau$ if the constraints of $C$ are satisfied*.
Our type inference program will generate a set of *constraints*, which ought to be *satisfied* for the type checker to succeed.
(Another change is the context $\Gamma$, which will now contain pairs $x : \sigma$ of variables and *polytypes* instead of pairs $x : \tau$ of variables and monotypes.)

Constraint solving
------------------

A *constraint* $\tau \sim \tau'$ states that $\tau$ and $\tau'$ should be *unified*.
The constraint $A \sim B \rightarrow \mathsf{Int}$, for example, asserts that the type variable $A$ should be equal to the type $B \rightarrow \mathsf{Int}$.
A *constraint set* $C$ is a set (or a list) of constraints.
We want to write a a function that *unifies* a constraint set.
This unification function will generate a substitution $\mathcal{S}$, such that the substitution *unifies* all constraints in $C$: for all constraints $\tau \sim \tau'$, $\mathcal{S} \tau$ (the substitution $\mathcal{S}$ applied tot type $\tau$) should be equal to $\mathcal{S} \tau'$.

In Haskell, we will create the following `Constraint` type, with the infix constructor `(:~:)` that corresponds to the $\sim$ in a constraint:

> data Constraint = Type :~: Type
>   deriving (Show)

For substitutions, we use a map:

> type Subst = Map String Type

The `substType` function will apply a substitution to a type.
Applying substitutions to monotypes (i.e., without $\forall$s) is quite easy, because we don't have to worry about renaming.

> substType :: Subst -> Type -> Type
> substType s TyBool = TyBool
> substType s TyInt  = TyInt

When we come across a type variable, we replace it by the corresponding type in the substitution, or keep it when the variable does not occur in the substitution:

> substType s (TyVar x) = Map.findWithDefault (TyVar x) x s

For function types, we just apply the substitution recursively:
  
> substType s (TyFun t1 t2) = TyFun (substType s t1) (substType s t2)

With the `substType` function, we can very easily apply a substitution to a constraint, by applying the substitution to the left-hand side and the right-hand side:

> substConstraint :: Subst -> Constraint -> Constraint
> substConstraint s (t1 :~: t2) = substType s t1 :~: substType s t2

We can also apply a substitution to a polytype $\forall \vec{X}. \tau$, which applies the substitution to $\tau$, with all elements from the substitution with a key from $\vec{X}$ removed:

> substPolytype :: Subst -> Polytype -> Polytype
> substPolytype s (TyForall xs ty) =
>   let s' = foldr Map.delete s xs
>    in TyForall xs (substType s' ty)

As we've seen in the previous post, substitution is generally quite hard for types which bind type variables, because the programmer might use the same type variable twice in different contexts, causing them to clash in some cases.
Luckily, this won't be a problem here, since the programmer doesn't write any type variables.
Instead, all type variables that we use are generated by the inference algorithm, which makes sure they are all unique (or *fresh*).
This will be explained later.

We also need to be able to compose two substitutions.
In mathematical notation, we write $\mathcal{S}_1 \circ \mathcal{S}_2$ for the composition of $\mathcal{S}_1$ and $\mathcal{S}_2$, where $\mathcal{S}_2$ is applied first.
We want $(\mathcal{S}_1 \circ \mathcal{S}_2)\tau$ for any type $\tau$ to be equal to $\mathcal{S}_1(\mathcal{S}_2\tau)$.
We first apply $\mathcal{S}_1$ to the codomain (that is, the *values*, not the keys, of the `Map`) of $\mathcal{S}_2$, and then return the union of the result and $\mathcal{S}_1$, where values of the first substitution are preferred:

> compose :: Subst -> Subst -> Subst
> compose s1 s2 = fmap (substType s1) s2 `Map.union` s1

Then, we can write the unification function for a single constraint:
  
<details>
<summary>The definition of `UnifyError`</summary>

> data UnifyError
>   = CannotUnify Type Type
>   | InfiniteType String Type
>   deriving (Show)

</details>

> unify :: Constraint -> Either UnifyError Subst
> unify c = case c of

To unify two equal simple types, we don't have to apply any substitution, so we'll just return an empty substitution:

>   TyBool :~: TyBool -> Right Map.empty
>   TyInt  :~: TyInt  -> Right Map.empty

To unify two function types, we just need to unify both parameter types and both target types.
We do this using the `solve` function, which can unify a list of constraints.
We'll define `solve` later.

>   TyFun t1 t2 :~: TyFun t1' t2' ->
>     solve [ t1 :~: t1'
>           , t2 :~: t2' ]

To unify a type variable with another type, we use the `bind` helper function, which we'll also define later.

>   t1      :~: TyVar x -> bind x t1
>   TyVar x :~: t2      -> bind x t2

Any other constraint is unsolvable, so we'll just throw an error:

>   t1 :~: t2 -> Left $ CannotUnify t1 t2

For unifying a type variable with another type, we use the `bind` function:

> bind :: String -> Type -> Either UnifyError Subst
> bind x t

When `t` is the same as the type variable `x`, we don't have to do any substituting:
  
>   | t == TyVar x   = Right Map.empty

When the type variable `x` occurs freely in `t` (and it is not `x` itself, which we have checked in the previous case), we cannot unify them, since that would require infinite types.
The constraint $X \sim X \rightarrow X$, for example, has no solution:
    
>   | x `occursIn` t = Left $ InfiniteType x t

Otherwise, we can just return the substitution which substitutes `x` for `t`:
    
>   | otherwise      = Right $ Map.fromList [(x, t)]

The `occursIn` function is very straight-forward:

> occursIn :: String -> Type -> Bool
> x `occursIn` t = case t of
>   TyBool      -> False
>   TyInt       -> False
>   TyFun t1 t2 -> x `occursIn` t1 || x `occursIn` t2
>   TyVar y     -> x == y

Finally, we can solve a list of constraints:

> solve :: [Constraint] -> Either UnifyError Subst

Solving an empty list of constraints just corresponds to doing nothing:
  
> solve [] = Right Map.empty

To solve a non-empty list of constraints, we first unify the constraint `c`, which gives us the substitution `s1`.
We apply this substitution to the rest of the constraints and solve the result, giving us the substitution `s2`, and then return the composition of `s2` and `s1`:
  
> solve (c:cs) = do
>   s1 <- unify c
>   s2 <- solve $ fmap (substConstraint s1) cs
>   Right (s2 `compose` s1)

Some examples:

< solve [TyVar "X" :~: TyInt]
<   => Right (fromList [("X",TyBool)])
<
< solve [TyInt :~: TyBool]
<   => Left (CannotUnify TyInt TyBool)
<
< solve [TyInt :~: TyVar "X", TyVar "X" :~: TyFun TyBool TyBool]
<   => Left (CannotUnify TyInt (TyFun TyBool TyBool))
<
< solve [TyInt :~: TyVar "X", TyVar "Y" :~: TyBool]
<   => Right (fromList [("X",TyInt),("Y",TyBool)])
<
< solve [TyVar "X" :~: TyFun (TyVar "X") (TyVar "X")]
<   => Left (InfiniteType "X" (TyFun (TyVar "X") (TyVar "X")))

We can also test whether `solve` has the desired behaviour, namely that the resulting substitution unifies the constraints.
To do this, we'll use the [QuickCheck](https://hackage.haskell.org/package/QuickCheck) library:

<details>
<summary>Testing `solve`</summary>

We will first need an instance of [`Arbitrary`](https://hackage.haskell.org/package/QuickCheck/docs/Test-QuickCheck.html#t:Arbitrary) for `Type` and `Constraint`.
The instance for `Type` is adapted from the [lambda calculus example](https://github.com/nick8325/quickcheck/blob/master/examples/Lambda.hs).
The frequency for `TyInt` and `TyBool` are relatively low, because a frequent occurrence of these simple types in the generated arbitrary types results in a lot of failed calls to `solve`.

> instance Arbitrary Type where
>   arbitrary = sized arbType
>    where
>     arbType n = frequency $
>       [ (10, TyVar <$> arbVar)
>       , (1, pure TyInt)
>       , (1, pure TyBool)
>       ] <>
>       [ (5, TyFun <$> arbType (n `div` 2) <*> arbType (n `div` 2))
>       | n > 0
>       ]
>     arbVar = elements [[c] | c <- ['A'..'Z']]
>
> instance Arbitrary Constraint where
>   arbitrary = (:~:) <$> arbitrary <*> arbitrary

Then we write the function `unifies`, which checks whether a substitution unifies the constraints.
(Remember: a substitution $\mathcal{S}$ satisfies a list of constraints $C$ if for all constraints $\tau \sim \tau'$ in $C$, $\mathcal{S}\tau = \mathcal{S}\tau'$.)

> unifies :: Subst -> [Constraint] -> Bool
> unifies s cs =
>   let cs' = fmap (substConstraint s) cs
>    in all (\(t1 :~: t2) -> t1 == t2) cs'

Now we can write our property, which will check whether every successful `solve` returns a substitution that unifies the list of constraints.
We will discard errors of `solve`, since they occur quite often for arbitrary constraints, but aren't useful for checking the property.

> prop_solveUnifies :: [Constraint] -> Property
> prop_solveUnifies cs =
>   case solve cs of
>     -- Discard errors
>     Left _      -> property Discard
>     Right subst -> property $ unifies subst cs

Now we can check the property:

< ghci> quickCheck prop_solveUnifies
< +++ OK, passed 100 tests; 637 discarded.

Looks good!
</details>

Typing rules
------------

Now we know how to solve constraints, but we don't know how to actually generate them.
The typing rules will generate the constraints that should be solves afterwards.

Let's first look at some easy rules.
The rules for the values of the simple types are the still the same as for the simply typed lambda calculus, with the addition of $\ldots \mid \varnothing$ at the end of the judgement, which states that the rules don't generate any constraints (an empty set):


The rule for applications is also not that hard:

$$
  \text{T-App: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      X \text{ fresh} \\
      C' = C_1 \cup C_2 \cup \{\tau_1 \sim \tau_2 \rightarrow X\}
    \end{array}
  }{
    \Gamma \vdash t_1\ t_2 : X \mid C'
  }
$$

When type checking the application $t_1\ t_2$, we first type check $t_1$ and $t_2$.
We then generate a new constraint set which consists of all the constraints of $C_1$, all of $C_2$ and the constraint $\tau_1 \sim \tau_2 \rightarrow X$.
(The $\cup$ symbol is mathematical notation for the [*union*](https://en.wikipedia.org/wiki/Union_%28set_theory%29) of two sets.)
Because $t_1$ is applied to $t_2$, $t_1$ should be a function with a parameter of the type of $t_2$.
We can't yet know the resulting type, so we use a fresh type variable, denoted by $X$, for which we add the constraint that $\tau_1$ should be equal to $\tau_2 \rightarrow X$.

To state that $X$ should be a freshly chosen type variable, we write $X \text{ fresh}$ in the typing rule.
A fresh type variable is a type variable which is not already used elsewhere.
Because all terms are implicitly typed (that is, they don't contain types in their syntax), we can confidently use a predefined list of fresh type variables, since there is no chance of them clashing with type variables written by the programmer (because they don't exist).

Other rules might add constraints regarding $X$.
The type inference of $t_1\ t_2 + 3$, for example, will add the constraint $X \sim \mathsf{Int}$.

The typing rules for if-then-else terms and addition terms are very easy: they are almost the same as for the simply typed lambda calculus, but now we can use constraints to specify that the condition of an if-then-else term must be a boolean, etc.:

$$
  \text{T-If: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      \Gamma \vdash t_3 : \tau_3 \mid C_3 \\
      C' = C_1 \cup C_2 \cup C_3 \cup \{\tau_1 \sim \mathsf{Bool}, \tau_2 \sim \tau_3\}
    \end{array}
  }{
    \Gamma \vdash \mathbf{if}\ t_1\ \mathbf{then}\ t_2\ \mathbf{else}\ t_3 : \tau_2 \mid C'
  }
$$

$$
  \text{T-Add: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      C' = C_1 \cup C_2 \cup \{\tau_1 \sim \mathsf{Int}, \tau_2 \sim \mathsf{Int}\}
    \end{array}
  }{
    \Gamma \vdash t_1 + t_2 : \mathsf{Int} \mid C'
  }
$$

The rule for variables is a bit more involved.
It looks like this:

$$
  \text{T-Var: } \frac{
    \begin{array}{c}
      x : \sigma \in \Gamma \\
      \tau = \mathit{inst}(\sigma)
    \end{array}
  }{
    \Gamma \vdash x : \tau \mid \varnothing
  }
$$

Remember that the context $\Gamma$ contains polytypes, but our typing relation uses monotypes ($\Gamma \vdash t : \tau$ instead of $\Gamma \vdash t : \sigma$).
To fix this, we use a function called $\mathit{inst}$ (short for 'instantiate'), which takes as its parameter a polytype $\forall \vec{X}. \tau$.
For every type variable $X_i$ in $\vec{X}$ (which is a list of type variables), it generates a new, fresh type variable $Y_i$.
It then performs the substitution $[X_1 := Y_1, \ldots, X_n := Y_n]$ on $\tau$ and returns the result.

This trick is necessary for *let-polymorphism* (which I'll discuss in more detail for the typing rule for let-in terms).
When inferring the type of the term
$$
\begin{array}{l}
  \mathbf{let}\ \mathsf{id} = \lambda x. x\ \mathbf{in} \\
  \mathbf{if}\ \mathsf{id}\ \mathsf{True}\ \mathbf{then}\ \mathsf{id}\ 4\ \mathbf{else}\ 5
\end{array}
$$
we would add $\mathsf{id} : \forall A. A \rightarrow A$ to the context.
When we come across the term $\mathsf{id}\ \mathsf{True}$, we would (without using $\mathit{inst}$) add the constraint $A \sim \mathsf{Bool}$.
But later, when we type check $\mathsf{if}\ 4$, we would also add the constraint $A \sim \mathsf{Int}$.
This results in an error, since the unification algorithm can't unify $\mathsf{Bool} \sim \mathsf{Int}$ (and rightly so).
$\mathit{inst}$ prevents this problem, as we'll see when looking at T-Let.

The rule for lambda abstractions looks like this:

$$
  \text{T-Abs: } \frac{
    \begin{array}{c}
      X \text{ fresh} \\
      \Gamma, x : \forall \varnothing. X \vdash t : \tau \mid C
    \end{array}
  }{
    \Gamma \vdash \lambda x. t : X \rightarrow \tau \mid C
  }
$$

This can be read as follows: *if $X$ is a free type variable and $\Gamma, x : \forall \varnothing. X$ entails that $t$ has type $\tau$ with the generated constraints $C$, then $\Gamma$ entails that $\lambda x. t$ has type $X \rightarrow \tau$ with the same generated constraint set $C$.*
Since the constraint set stays the same, the T-Abs rule does not introduce any constraints.

Because lambda abstractions are no longer annotated with the type of the parameter ($\lambda x : \tau. t$), we don't know what type we should give $x$ in the context to type check the body of the lambda abstraction ($t$).
We therefore use a fresh type variable $X$ as $x$'s type.
But, since the context contains polytypes, we can't just add the pair $x : X$.
We instead add the pair $x : \forall \varnothing. X$.

Not binding $X$ with a $\forall$ (i.e., adding $x : \forall X. X$) prevents $\mathit{inst}$ from applying let-polymorphism to the arguments of lambda abstractions.
The above example using a let-in term would not work as a lambda abstraction: $(\lambda \mathsf{id}. \mathbf{if}\ \mathsf{id}\ \mathsf{True}\ \mathbf{then}\ \mathsf{id}\ 4\ \mathbf{else}\ 5)\ (\lambda x. x)$ would fail to type check.

The rule for let-in terms, finally, looks like this:

$$
  \text{T-Let: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \mathcal{S} = \mathit{solve}(C_1) \\
      \sigma = \mathit{gen}(\mathcal{S}\Gamma, \mathcal{S}\tau_1) \\
      \Gamma, x : \sigma \vdash t_2 : \tau_2 \mid C_2
    \end{array}
  }{
    \Gamma \vdash \mathbf{let}\ x = t_1\ \mathbf{in}\ t_2 : \tau_2 \mid C_2
  }
$$

This rule is executed in the following steps:

1. The type of $t_1$ is determined.
2. The constraints generated while inferring the type of $t_1$ are solved using the `solve` function, giving us the substitution $\mathcal{S}$.
3. The substitution is applied to the context $\Gamma$ and $\tau_1$ and the resulting type is *generalised* (using the $\mathit{gen}$ function).
   The $\mathit{gen}$ function creates a polytype $\sigma$ of the form $\forall \vec{X}. \mathcal{S}\tau_1$ for the monotype $\mathcal{S}\tau_1$ in which all free type variables $\vec{X}$ of $\mathcal{S}\tau_1$ (not occurring in $\mathcal{S}\Gamma$) are bound by a $\forall$.
4. The type of $t_2$ is determined with $x : \sigma$ added to the context.

This rule adds *let-polymorphism* to the language.
These quite complicated steps are necessary to actually make use of polymorphism.
As we saw before, we want lambda abstractions to not support polymorphism, so a parameter can only be used on one concrete type.
But for let-in terms, we do want to be able to use the bound variable on multiple concrete types: the identity function on booleans, integers, integer-to-boolean functions, etc.

In the rule for variables, T-Var, we introduced the $\mathit{inst}$ function.
It creates a fresh type variable for every type variable bound in a polytype.
To prevent it from generalising the parameters of lambda abstractions, we didn't bind any type variables in the polytype we added to the context: $\forall \varnothing. X$.
For let-in terms, however, we do want $\mathit{inst}$ to create another instance for the bound variable for every occurrence.
Therefore, we find the most general type for the variable, and add it to the context.
When type checking the term $\mathbf{let}\ \mathsf{id} = \lambda x. x\ \mathbf{in}\ \mathsf{id}\ 1$, for example, $\mathsf{id}$ is added to the context with its most general type: $\forall X. X \rightarrow X$.
When typing the body of the let-in term, then, the type of $\mathsf{id}$ is instantiated as $Y \rightarrow Y$ for example.
Then the constraint $Y \sim \mathsf{Int}$ is generated, because $\mathsf{id}$ is applied to $1$, but $X$ is still untouched.

With these typing rules, we can move on to implementing the type inference algorithm.

Implementation
--------------

For the implementation, we will use so-called [monad transformers](https://hackage.haskell.org/package/mtl).
However, you should not need to understand how monad transformers work in order to understand the implementation.

Our inference monad looks like this:

> type Infer a = RWST Context [Constraint] [String] (Except TypeError) a
>
> type Context = Map String Polytype

<details>
<summary>The definition of `TypeError`</summary>
 
> data TypeError

The variable was not bound by a lambda abstraction.
  
>   = UnboundVariable String

An error occurred during unification.

>   | UnifyError UnifyError

>   deriving (Show)

</details>

The inference monad is a `Reader` monad for the `Context`, which is practically the same as having a `Context` parameter for every function inside the `Infer` monad, which is what we did before.
Everywhere inside the `Infer` monad we can get the context, but we can't change it.
`Infer` is also a `Writer` for a list of `Constraint`s, which means that we can write to a list of constraints.
This list of constraints is the $\ldots \mid C$ in the typing rules.
`Infer` is furthermore a `State` for a list of `String`s, which will be the supply of fresh type variables.
And lastly, `Infer` can throw `TypeError`s.

Using `runInfer`, we can convert a value of `Infer a` to an `Either TypeError (a, [String], [Constraint])`:

> runInfer :: Context
>          -> [String]
>          -> Infer a
>          -> Either TypeError (a, [String], [Constraint])
> runInfer ctx fs m = runExcept $ runRWST m ctx fs

First, we need a function that generates a fresh type variable.
The state should be an infinite list of type variable names, so we should always be able to get the following element from the list:

> fresh :: Infer String
> fresh = do
>   freshVars <- get
>   case freshVars of
>     []     -> error "Non-infinite list of fresh type variables."
>     (f:fs) -> do
>       put fs
>       pure f

With `get :: Infer [String]` we can get the list of type variables.
When it's empty, we just use `error` since the programmer has made a mistake by not using an infinite list of fresh type variables.
When the list is non-empty, we return the `head`, and we use the `tail` as the new state by using `put :: [String] -> Infer ()`, which replaces the state.

For the initial state of fresh variables, we will use the following:

> freshVariables :: [String]
> freshVariables = concatMap (\n -> [l : n | l <- ['A'..'Z']]) $
>   "" : fmap show [1..]

This list will look something like:

< ["A", "B", ..., "Z", "A1", "B1", ..., "Z1", "A2", "B2", ...]

We will also need the `inst` function:

> inst :: Polytype -> Infer Type
> inst (TyForall xs ty) = do
>   ys <- mapM (const fresh) xs
>   let subst = Map.fromList $ zip xs (fmap TyVar ys)
>   pure $ substType subst ty

For every type variable $X$ bound by the $\forall$, we create a fresh type variable $Y$.
Then we apply the substitution which substitutes every $X_i$ for $Y_i$.

We also need the `gen` function, but before we can write it, we need to be able to get the set of free type variables from a type:

> freeVarsType :: Type -> Set String
> freeVarsType TyBool        = Set.empty
> freeVarsType TyInt         = Set.empty
> freeVarsType (TyVar x)     = Set.singleton x
> freeVarsType (TyFun t1 t2) = freeVarsType t1 `Set.union` freeVarsType t2

And the free type variables from a polytype, which are the free type variables in the monotype that are not bound by the $\forall$.

> freeVarsPolytype :: Polytype -> Set String
> freeVarsPolytype (TyForall xs ty) = freeVarsType ty `Set.difference` Set.fromList xs

And also from the context, which corresponds to the union of the free type variables of all polytypes in the context: 

> freeVarsContext :: Context -> Set String
> freeVarsContext = foldMap freeVarsPolytype

Now we can write `gen`.
We will write it outside the `Infer` monad, because it will be useful elsewhere too.

> gen :: Context -> Type -> Polytype
> gen ctx ty =
>   let xs = Set.toList (freeVarsType ty `Set.difference` freeVarsContext ctx)
>    in TyForall xs ty

`gen` just finds the free type variables of `ty` which don't occur in the context, and returns a polytype in which those type variables are bound.

We will also need to be able to apply a substitution to a context, by applying the substitution to every polytype in the context:

> substContext :: Subst -> Context -> Context
> substContext s = fmap (substPolytype s)

Now we can finally implement the type inference algorithm:

> infer :: Term -> Infer Type

$$
  \text{T-False: } \frac{
  }{
    \varnothing \vdash \mathsf{True} : \mathsf{Bool} \mid \varnothing
  }
$$

$$
  \text{T-True: } \frac{
  }{
    \varnothing \vdash \mathsf{True} : \mathsf{Bool} \mid \varnothing
  }
$$

$$
  \text{T-Int: } \frac{
  }{
    \varnothing \vdash n : \mathsf{Int} \mid \varnothing
  }
$$

Values of the simple types are, of course, easy:
  
> infer TmFalse   = pure TyBool
> infer TmTrue    = pure TyBool
> infer (TmInt _) = pure TyInt

$$
  \text{T-App: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      X \text{ fresh} \\
      C' = C_1 \cup C_2 \cup \{\tau_1 \sim \tau_2 \rightarrow X\}
    \end{array}
  }{
    \Gamma \vdash t_1\ t_2 : X \mid C'
  }
$$

For applications:

> infer (TmApp t1 t2) = do

We first infer the types of `t1` and `t2`:
  
>   ty1 <- infer t1
>   ty2 <- infer t2

We generate a fresh type variable `f`:
  
>   f <- TyVar <$> fresh

We generate the constraint `ty1 :~: TyFun ty2 f`.
We can add it to the list of constraints using the `tell :: [Constraint] -> Infer ()` function.
 
>   tell [ty1 :~: TyFun ty2 f]

Finally, we return the fresh type variable as the type:
  
>   pure f

$$
  \text{T-If: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      \Gamma \vdash t_3 : \tau_3 \mid C_3 \\
      C' = C_1 \cup C_2 \cup C_3 \cup \{\tau_1 \sim \mathsf{Bool}, \tau_2 \sim \tau_3\}
    \end{array}
  }{
    \Gamma \vdash \mathbf{if}\ t_1\ \mathbf{then}\ t_2\ \mathbf{else}\ t_3 : \tau_2 \mid C'
  }
$$

For if-then-else terms, we generate the constraints that the condition should be a boolean and that the arms should be of the same type :

> infer (TmIf t1 t2 t3) = do
>   ty1 <- infer t1
>   ty2 <- infer t2
>   ty3 <- infer t3
>   tell [ty1 :~: TyBool, ty2 :~: ty3]
>   pure ty2

$$
  \text{T-Add: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \Gamma \vdash t_2 : \tau_2 \mid C_2 \\
      C' = C_1 \cup C_2 \cup \{\tau_1 \sim \mathsf{Int}, \tau_2 \sim \mathsf{Int}\}
    \end{array}
  }{
    \Gamma \vdash t_1 + t_2 : \mathsf{Int} \mid C'
  }
$$

The operands of an addition should be integers, and the result is also an integer:

> infer (TmAdd t1 t2) = do
>   ty1 <- infer t1
>   ty2 <- infer t2
>   tell [ty1 :~: TyInt, ty2 :~: TyInt]
>   pure TyInt

$$
  \text{T-Var: } \frac{
    \begin{array}{c}
      x : \sigma \in \Gamma \\
      \tau = \mathit{inst}(\sigma)
    \end{array}
  }{
    \Gamma \vdash x : \tau \mid \varnothing
  }
$$

For variables, we use the `inst` function:

> infer (TmVar x) = do

We can get the context using `ask`:
  
>   ctx <- ask

We look up `x`:

>   case Map.lookup x ctx of

When it doesn't exist in the context, we use `throwError :: TypeError -> Infer ()` to throw an error:
  
>     Nothing -> throwError $ UnboundVariable x

Otherwise, we use `inst` on the type:

>     Just ty -> inst ty

$$
  \text{T-Abs: } \frac{
    \begin{array}{c}
      X \text{ fresh} \\
      \Gamma, x : \forall \varnothing. X \vdash t : \tau \mid C
    \end{array}
  }{
    \Gamma \vdash \lambda x. t : X \rightarrow \tau \mid C
  }
$$

Then lambda abstractions.
Using `local :: (Context -> Context) -> Infer a -> Infer a` we can update the context for a local sub-computation.
To infer the type of `t`, we need to add `x`'s type to the context, so we use `local`.
Note that the context is not changed in the outer computation:

> infer (TmAbs x t) = do
>   f <- TyVar <$> fresh 
>   ty <- local (Map.insert x (TyForall [] f)) $ infer t
>   pure $ TyFun f ty

$$
  \text{T-Let: } \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \tau_1 \mid C_1 \\
      \mathcal{S} = \mathit{solve}(C_1) \\
      \sigma = \mathit{gen}(\mathcal{S}\Gamma, \mathcal{S}\tau_1) \\
      \Gamma, x : \sigma \vdash t_2 : \tau_2 \mid C_2
    \end{array}
  }{
    \Gamma \vdash \mathbf{let}\ x = t_1\ \mathbf{in}\ t_2 : \tau_2 \mid C_2
  }
$$

And, finally, let-in terms:

> infer (TmLet x t1 t2) = do

We first get the context:

>   ctx <- ask

Then we use `listen :: Infer a -> Infer (a, [Constraint])` to 'listen' to the constraints generated by `infer t1`.
These constraints will not be added to the final list of constraints, but are only generated 'locally':
  
>   (ty1, cs) <- listen $ infer t1

Now we try to solve the constraints.
If they're not solvable, we just throw an error.
Otherwise, we obtain a substitution:
  
>   subst <- case solve cs of
>     Left e  -> throwError $ UnifyError e
>     Right s -> pure s

We apply the substitution to `t1`'s type, `ty1`, giving us `ty1'`.

>   let ty1' = substType subst ty1

And we generalise `ty1'` in the context to which we have also applied the substitution, giving us a polytype `s`:
        
>   let s = gen (substContext subst ctx) ty1'

We add `s` to the context and infer `t2`'s type:

>   local (Map.insert x s) $ infer t2

That's it!
We've written an function which runs the inference algorithm on a term, giving us a type and a list of constraints.

Now, we still need to solve the constraints and apply the substitution to the type.
We will write the function `polytypeOf`, which runs the inference algorithm, solves the constraints, applies the substitution, and turns the resulting type into a polytype:

> polytypeOf :: Term -> Either TypeError Polytype
> polytypeOf t = do

Run the inference algorithm in an empty context[^empty-context], giving us a type `ty`, a list of fresh variables `fs` and a list of constraints `cs`:

[^empty-context]: If you want to extend the language by having declarations, or by making a REPL, you might want to run `infer` in a specific context, so declarations aren't lost.
  You would also have to run `gen` with this context, instead of an empty context.
  
>   (ty, fs, cs) <- runInfer Map.empty freshVariables $ infer t

Solve the constraints to obtain a substitution.
Because `solve` returns an `Either UnifyError Subst`, we need to turn its error into a `TypeError`, which we can do by applying the type constructor `TypeError` to it.
To do this, we use `first :: Bifunctor p => (a -> b) -> p a c -> p b c`:
  
>   subst <- first UnifyError $ solve cs

We apply the substitution to `ty`:
  
>   let ty' = substType subst ty

We generalise the type in an empty context, giving us the polytype `s`:

>   let s = gen Map.empty ty'

And we return `s`:

>   Right s

Let's try it!

The type of `id`:

> polytypeOf tmId
>   => Right (TyForall ["A"] (TyFun (TyVar "A") (TyVar "A")))

That is $\forall A. A \rightarrow A$, correct!

The type of `const`:

> polytypeOf tmConst
>   => Right (TyForall ["A","B"] (TyFun (TyVar "A") (TyFun (TyVar "B") (TyVar "A"))))

$\forall A\ B. A \rightarrow B \rightarrow A$, again correct!

Now let's try to use let-polymorphism, by trying the term:
$$
\begin{array}{l}
  \mathbf{let}\ \mathsf{id} = \lambda x. x\ \mathbf{in} \\
  \mathbf{if}\ \mathsf{id}\ \mathsf{True}\ \mathbf{then}\ \mathsf{id}\ 4\ \mathbf{else}\ 5
\end{array}
$$

> polytypeOf (TmLet "id" (TmAbs "x" (TmVar "x")) (TmIf (TmApp (TmVar "id") TmTrue) (TmApp (TmVar "id") (TmInt 4)) (TmInt 5)))
>   => Right (TyForall [] TyInt)

And the same term, but using a lambda abstraction:

$$
  (\lambda \mathsf{id}. \mathbf{if}\ \mathsf{id}\ \mathsf{True}\ \mathbf{then}\ \mathsf{id}\ 4\ \mathbf{else}\ 5)\ (\lambda x. x)
$$

> polytypeOf (TmApp (TmAbs "id" (TmIf (TmApp (TmVar "id") TmTrue) (TmApp (TmVar "id") (TmInt 4)) (TmInt 5))) (TmAbs "x" (TmVar "x")))
>   => Left (UnifyError (CannotUnify TyBool TyInt))

Just like we expected, it can't unify $\mathsf{Bool} \sim \mathsf{Int}$.

One more:
$$
\begin{array}{l}
  \mathbf{let}\ \mathsf{id} = \lambda x. x\ \mathbf{in} \\
  \mathbf{let}\ \mathsf{const} = \lambda a. \lambda b. a\ \mathbf{in} \\
  \mathsf{const}\ \mathsf{id}\ \mathsf{const}
\end{array}
$$

> polytypeOf $ TmLet "id" tmId $ TmLet "const" tmConst $ TmApp (TmApp (TmVar "const") (TmVar "id")) (TmVar "const")
>   => Right (TyForall ["F"] (TyFun (TyVar "F") (TyVar "F")))

It returns $\forall F. F \rightarrow F$, which is exactly the type of $\mathsf{id}$.

Conclusion
==========

We've explored Hindley-Milner type inference, and implemented a type inference algorithm!
This language is already quite close to Haskell.

Some exercises you might like to do:

1. Write a function `simplPolytype` which 'simplifies' a polytype.
   It should rename the bound variables in a polytype to names in the beginning of the alphabet (or: the beginning of `freshVariables`).
   The polytype of the last example is $\forall F. F \rightarrow F$, for example, but it would be nicer if `polytypeOf` returned $\forall A. A \rightarrow A$.
2. Extend the language using other simple types and operations for them.

And, if you have trouble understanding some parts, try to experiment with them a lot.
And feel free to ask questions on Reddit (the link to the Reddit thread should be added after the post is made).

Further reading
---------------

Other resources you might find useful:

- [*Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/), Benjamin C. Pierce, Chapters 22 and 23.
- [*Hindley-Milner type system*](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) on Wikipedia.
- [*Hindley-Milner inference*](http://dev.stephendiehl.com/fun/006_hindley_milner.html), chapter 6 of Stephen Diehl's *Write You a Haskell*.
