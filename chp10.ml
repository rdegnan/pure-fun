(*
   Original source code in SML from:

     Purely Functional Data Structures
     Chris Okasaki
     Cambridge University Press, 1998
     Copyright (c) 1998 Cambridge University Press

   Translation from SML to OCAML (this file):

     Copyright (C) 2012  Ryland Degnan
     email:  ryland.degnan@mrnumber.com
     www:    http://www.mrnumber.com

   Licensed under the Apache License, Version 2.0 (the "License"); you may
   not use this file except in compliance with the License.  You may obtain
   a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
   License for the specific language governing permissions and limitations
   under the License.
*)

(************************************************************************)
(*                              Chapter 10                              *)
(************************************************************************)

exception Empty
exception Subscript
exception Impossible_pattern of string

let impossible_pat x = raise (Impossible_pattern x)


module type RANDOM_ACCESS_LIST = sig
  type 'a ra_list

  val empty : 'a ra_list
  val is_empty : 'a ra_list -> bool

  val cons : 'a -> 'a ra_list -> 'a ra_list
  val head : 'a ra_list -> 'a
  val tail : 'a ra_list -> 'a ra_list
    (* head and tail raise Empty if list is empty *)

  val lookup : int -> 'a ra_list -> 'a
  val update : int -> 'a -> 'a ra_list -> 'a ra_list
    (* lookup and update raise Subscript if index is out of bounds *)
end


module AltBinaryRandomAccessList : RANDOM_ACCESS_LIST = struct
	type 'a ra_list = Nil | Zero of ('a * 'a) ra_list | One of 'a * ('a * 'a) ra_list

	let empty = Nil
	let is_empty = function Nil -> true | _ -> false

	let rec cons : 'a . 'a -> 'a ra_list -> 'a ra_list =
	  fun x -> function
	    | Nil         -> One (x, Nil)
	    | Zero    ps  -> One (x, ps)
	    | One (y, ps) -> Zero (cons (x, y) ps)

	let rec uncons : 'a . 'a ra_list -> 'a * 'a ra_list = function
	  | Nil          -> raise Empty
	  | One (x, Nil) -> x, Nil
	  | One (x, ps ) -> x, Zero ps
	  | Zero    ps   ->
	      let (x, y), qs = uncons ps in
	      x, One (y, qs)

	let head xs = let x, _  = uncons xs in x
	let tail xs = let _, xs' = uncons xs in xs'

	let rec lookup : 'a . int -> 'a ra_list -> 'a =
	  fun i -> function
	    | Nil                    -> raise Subscript
	    | One (x, _ ) when i = 0 -> x
	    | One (_, ps)            -> lookup (i - 1) (Zero ps)
	    | Zero ps                ->
	        let (x, y) = lookup (i / 2) ps in
	        if i mod 2 = 0 then x else y

	let rec fupdate : 'a . ('a -> 'a) -> int -> 'a ra_list -> 'a ra_list =
	  fun f i -> function
	    | Nil                    -> raise Subscript
	    | One (x, ps) when i = 0 -> One (f x, ps)
	    | One (x, ps)            -> cons x (fupdate f (i - 1) (Zero ps))
	    | Zero ps                ->
	        let f' (x, y) = if i mod 2 = 0 then (f x, y) else (x, f y) in
	        Zero (fupdate f' (i / 2) ps)

	let update i y = fupdate (fun x -> y) i
end


let (!$) = Lazy.force

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool

  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a        (* raises Empty if queue is empty *)
  val tail : 'a queue -> 'a queue  (* raises Empty if queue is empty *)
end


module BootstrappedQueue : QUEUE = struct
  type 'a queue = E | Q of int * 'a list * 'a list Lazy.t queue * int * 'a list

  let empty = E
  let is_empty = function E -> true | _ -> false

  let rec checkq : 'a . int * 'a list * 'a list Lazy.t queue * int * 'a list -> 'a queue =
    fun ((lenfm, f, m, lenr, r) as q) ->
      if lenr <= lenfm then checkf q
      else checkf (lenfm + lenr, f, snoc m (lazy (List.rev r)), 0, [])

  and checkf : 'a . int * 'a list * 'a list Lazy.t queue * int * 'a list -> 'a queue =
    fun (lenfm, f, m, lenr, r) ->
      match f, m with
        | [], E -> E
        | [], _ -> Q (lenfm, !$(head m), tail m, lenr, r)
        | _ -> Q (lenfm, f, m, lenr, r)

  and snoc : 'a . 'a queue -> 'a -> 'a queue =
    fun q x ->
      match q with
        | E -> Q (1, [x], E, 0, [])
        | Q (lenfm, f, m, lenr, r) ->
            checkq (lenfm, f, m, lenr + 1, x::r)

  and head : 'a. 'a queue -> 'a = function
    | E -> raise Empty
    | Q (lenfm, x::f', m, lenr, r) -> x
    | _ -> impossible_pat "head"

  and tail : 'a. 'a queue -> 'a queue = function
    | E -> raise Empty
    | Q (lenfm, x::f', m, lenr, r) ->
        checkq (lenfm - 1, f', m, lenr, r)
    | _ -> impossible_pat "tail"
end


module type CATENABLE_LIST = sig
  type 'a cat

  val empty : 'a cat
  val is_empty : 'a cat -> bool

  val cons : 'a -> 'a cat -> 'a cat
  val snoc : 'a cat -> 'a -> 'a cat
  val append : 'a cat -> 'a cat -> 'a cat

  val head : 'a cat -> 'a
  val tail : 'a cat -> 'a cat
end


module CatenableListImpl (Q : QUEUE) : CATENABLE_LIST = struct
  type 'a cat = E | C of 'a * 'a cat Lazy.t Q.queue

  let empty = E
  let is_empty = function E -> true | _ -> false

  let link xs s = match xs with
    | C (x, q) -> C (x, Q.snoc q s)
    | _ -> impossible_pat "link"

  let rec link_all q =
    let t = !$ (Q.head q) in
    let q' = Q.tail q in
    if Q.is_empty q' then t else link t (lazy (link_all q'))

  let append xs1 xs2 = match xs1, xs2 with
    | E, _ -> xs2
    | _, E -> xs1
    | _ -> link xs1 (lazy xs2)

  let cons x xs = append (C (x, Q.empty)) xs
  let snoc xs x = append xs (C (x, Q.empty))

  let head = function
    | E -> raise Empty
    | C (x, _) -> x

  let tail = function
    | E -> raise Empty
    | C (x, q) -> if Q.is_empty q then E else link_all q
end


(* A totally ordered type and its comparison functions *)
module type ORDERED = sig
  type t

  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val leq : t -> t -> bool
end


module type HEAP = sig
  module Elem : ORDERED

  type heap

  val empty : heap
  val is_empty : heap -> bool

  val insert : Elem.t -> heap -> heap
  val merge : heap -> heap -> heap

  val find_min : heap -> Elem.t  (* raises Empty if heap is empty *)
  val delete_min : heap -> heap  (* raises Empty if heap is empty *)
end


module Bootstrap (MakeH : functor (Element : ORDERED) -> (HEAP with module Elem = Element))
  (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  module rec BootstrappedElem : sig
    type t = E | H of Elem.t * PrimH.heap

    val eq : t -> t -> bool
    val lt : t -> t -> bool
    val leq : t -> t -> bool
  end = struct
    type t = E | H of Elem.t * PrimH.heap

    let eq x y = match x, y with
      | H (x, _), H (y, _) -> Elem.eq x y
      | _ -> impossible_pat "eq"

    let lt x y = match x, y with
      | H (x, _), H (y, _) -> Elem.lt x y
      | _ -> impossible_pat "lt"

    let leq x y = match x, y with
      | H (x, _), H (y, _) -> Elem.leq x y
      | _ -> impossible_pat "leq"
  end
  and PrimH : (HEAP with type Elem.t = BootstrappedElem.t) = MakeH (BootstrappedElem)

  open BootstrappedElem (* expose E and H constructors *)

  type heap = BootstrappedElem.t

  let empty = E
  let is_empty = function E -> true | _ -> false

  let merge h1 h2 = match h1, h2 with
    | E, h -> h
    | h, E -> h
    | H (x, p1), H (y, p2) ->
        if Elem.leq x y then H (x, PrimH.insert h2 p1)
        else H (y, PrimH.insert h1 p2)

  let insert x h = merge (H (x, PrimH.empty)) h

  let find_min = function
    | E -> raise Empty
    | H (x, _) -> x

  let delete_min = function
    | E -> raise Empty
    | H (x, p) ->
        if PrimH.is_empty p then E
        else match PrimH.find_min p with
          | H (y, p1) ->
              let p2 = PrimH.delete_min p in
              H (y, PrimH.merge p1 p2)
          | _ -> impossible_pat "delete_min"
end
