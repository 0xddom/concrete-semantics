theory Chapter2
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done


(* Exercise 2.1: Use the value command to evaluate the following expressions: *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2: Start from the definition of add given above. Prove that add 
   is associative and commutative. Define a recursive function double :: nat \<Rightarrow> nat
   and prove double m = add m m. *)
lemma add_assoc [simp]: "add (add a b) c = add a (add b c)"
  apply(induction a)
  apply(auto)
  done

lemma add_assoc1 [simp]: "add n (Suc m) = add (Suc n) m"
  apply(induction n)
   apply(auto)
  done

lemma add_comm: "add a b = add b a"
  apply(induction a)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma double_eq_add_itself: "double n = add n n"
  apply(induction n)
   apply(auto)
  done

(* Exercise 2.3: Define a function count :: 'a \<Rightarrow> 'a list \<Rightarrow> nat that counts the number
   of occurrences of an element in a list. Prove count x xs \<le> length xs. *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ [] = 0" |
"count x (y # xs) = (if x = y then Suc (count x xs) else count x xs)"

lemma never_count_more_than_len: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.4: Define a recursive function snoc : 'a list \<Rightarrow> 'a \<Rightarrow> 'a list
   that appends an element to the end of a list. With the help of snoc define a recursive function
   reverse :: 'a list \<Rightarrow> 'a list that reverses a list. Prove reverse (reverse xs) = xs. *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] e = [e]" |
"snoc (x # xs) e = x # (snoc xs e)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_app [simp]: "reverse (snoc xs y) = y # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

lemma reverse_twice: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.5: Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
   sum_upto n = 0 + ... + n and prove sum_upto n = n * (n + 1_) div 2. *)
fun sum_upto :: "nat \<Rightarrow> nat" where 
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + sum_upto n"

lemma gauss: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
  done

(* Exercise 2.6. Starting from the type \<Zprime>a tree defined in the text, define a function 
   contents :: \<Zprime>a tree \<Rightarrow> \<Zprime>a list that collects all values in a tree in a list, in any order, 
   without removing duplicates. Then define a function sum_tree :: nat tree \<Rightarrow> nat that sums up 
   all values in a tree of natural numbers and prove sum_tree t = sum_list (contents t) 
   (where sum_list is predefined). *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l v r) = contents l @ (v # contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l v r) = sum_tree l + v + sum_tree r"

lemma sum_tree_lemma: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done

(* Exercise 2.7. Define the two functions pre_order and post_order of type \<Zprime>a tree \<Rightarrow> \<Zprime>a list 
   that traverse a tree and collect all stored values in the respective order in a list. 
   Prove pre_order (mirror t) = rev (post_order t). *)
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = a # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l v r) = post_order l @ post_order r @ [v]"

lemma pre_order_of_mirror_eq_rev_post_order: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

(* Exercise 2.8. Define a function intersperse :: \<Zprime>a \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list such that 
   intersperse a [x1, ..., xn] = [x1, a, x2, a, ..., a, xn]. Now prove that 
   map f (intersperse a xs) = intersperse (f a) (map f xs). *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # xs) = x # (a # (intersperse a xs))"

lemma map_comm: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
    apply(auto)
  done

(* Exercise 2.9. Write a tail-recursive variant of the add function on nat: itadd. 
   Tail-recursive means that in the recursive case, itadd needs to call itself 
   directly: itadd (Suc m) n = itadd .... Prove itadd m n = add m n. *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_works: "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

(* Exercise 2.10. Define a datatype tree0 of binary tree skeletons which do not 
   store any information, neither in the inner nodes nor in the leaves. Define a 
   function nodes :: tree0 \<Rightarrow> nat that counts the number of all nodes (inner nodes 
   and leaves) in such a tree. *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = Suc (nodes l + nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where 
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

abbreviation  exp_nodes :: "tree0 \<Rightarrow> nat \<Rightarrow> nat" where
"exp_nodes t n \<equiv> nodes t ^ n" (* WIP *)

(* Find an equation expressing the size of a tree after exploding it 
   (nodes (explode n t)) as a function of nodes t and n. Prove your equation. 
   You may use the usual arithmetic operators, including the exponentiation 
   operator “^”. For example, 2 ^ 2 = 4.
   Hint: simplifying with the list of theorems algebra_simps takes care of 
   common algebraic properties of the arithmetic operators. *)

lemma nodes_01: "nodes (explode n t) = exp_nodes t n"
  apply (induction t)
  apply(auto) (* WIP *)


end