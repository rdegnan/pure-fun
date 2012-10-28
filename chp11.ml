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
(*                              Chapter 11                              *)
(************************************************************************)

exception Empty
exception Subscript
exception Impossible_pattern of string

let impossible_pat x = raise (Impossible_pattern x)


let (!$) = Lazy.force

module type QUEUE = sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool

  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a        (* raises Empty if queue is empty *)
  val tail : 'a queue -> 'a queue  (* raises Empty if queue is empty *)
end


module ImplicitQueue : QUEUE = struct
   type 'a digit = Zero | One of 'a | Two of 'a * 'a
   type 'a queue = Shallow of 'a digit | Deep of 'a digit * ('a * 'a) queue Lazy.t * 'a digit

   let empty = Shallow Zero
   let is_empty = function Shallow Zero -> true | _ -> false

   let rec snoc : 'a. 'a queue -> 'a -> 'a queue = fun q y ->
     match q with
       | Shallow Zero -> Shallow (One y)
       | Shallow (One x) -> Deep (Two (x,y), lazy empty, Zero)
       | Deep (f, m, Zero) -> Deep (f, m, One y)
       | Deep (f, m, One x) -> Deep (f, lazy (snoc (!$m) (x,y)), Zero)
       | _ -> impossible_pat "snoc"

   and head : 'a. 'a queue -> 'a = function
     | Shallow Zero -> raise Empty
     | Shallow (One x) -> x
     | Deep (One x, m, r) -> x
     | Deep (Two (x,y), m, r) -> x
     | _ -> impossible_pat "head"

   and tail : 'a. 'a queue -> 'a queue = function
     | Shallow Zero -> raise Empty
     | Shallow (One x) -> empty
     | Deep (Two (x,y), m, r) -> Deep (One y, m, r)
     | Deep (One x, lazy q, r) ->
         if is_empty q then Shallow r
         else let (y,z) = head q in
              Deep (Two (y,z), lazy (tail q), r)
     | _ -> impossible_pat "tail"
end
