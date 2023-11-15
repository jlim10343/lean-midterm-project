# AJ and George's Lean Midterm Project

For this midterm project, we decided to replicate some of proofs regarding
structural induction.

## Lists

- We first define the `list` `datatype` and some critical functions behind them,
such as `map`, `append`, and `len`.

- We prove simple results relating to append, which is the fact that for all
values `A : List` $\alpha$ and `B : List` $\alpha$, and total functions `f :`
$\alpha \to \beta$ we have,

```sml
map f (A @ B) = (map f A) @ (map f B)
len (A @ B) = len A + len B
```

- We then noticed that both the proofs are pretty much the same. Is there a way
to creater one singular proof about appending and these functions?

- There is, and it uses the function called `fold`, which is a generic for-loop
across a list:
```sml
fun fold g z [] = z
  | fold g z (x::xs) = g x (foldl g z xs)
```
- In short, `fold g z [x1, x2, ..., xn] = g(x1, g(x2, ..., g(xn, z)...))`. Now,
we can show that for all values `A : List` $\alpha$, values `B : List` $\beta$, values `g :` $\alpha \to \beta \to \beta$,
and all values `z :` $\beta$, that
```sml
fold g z (A @ B) = fold g (fold g z B) A
```

- We can now rewrite `map` via the following:
```sml
val map' f = fold (fn (x, L) => (f x)::L) []
```
- We can easily prove the equivalence from the old `map` to the new `map'`.
However, we realized that it's impossible to prove with the new `map'` that
`map' f (A @ B) = (map' f A) @ (map' f B)`. The code we currently have is not
strong enough. We instead write a stronger function:
```sml
val map' f B = fold (fn x, L => (f x)::L) B
```
- Here, we can now show that `map' f B A = (map f A) @ B`, so we can kind of
accumulate results. Now, we can prove that `(map f A) @ (map f B)` by redefinin
`map f A` to `map' f [] A`, so we can easily prove the theorem without redoing
all the work over and over again.

- A similar conversion can be done for `len`, where we can define as below.
However, we have left writing this out in lean an exercise for the reader
```sml
val len' acc = foldl (fn (_, tot) => tot + 1) acc
```

## Trees
- We first define the `tree` `datatype` and some critical functions like 
`treeMap`, `inord` (traversal), `leaves`, `trim`, and `size`.
  - `treeMap` applies a mapping function to each element in the tree
  - `inord` gives a list that's the inorder traversal of the tree (left, then
    root, then right)
  - `leaves` returns all leaves of the tree
  - `trim` removes all leaves of the tree

- We don't go extensively in depth like above. However, we prove the following
theorems for all values `T : Tree` $\alpha$, and total values `f :` $\alpha \to \beta$
```sml
inord (treeMap f T) = map f (inord T)
size (trim T) + len (leaves T) = size T
```
