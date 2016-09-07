type 'elt tree =
  | Node of 'elt tree * 'elt * 'elt tree
  | Leaf

let rec format_tree format_elt ppf = function
  | Leaf ->
    Format.fprintf ppf ""
  | Node (left,root,right) ->
    Format.fprintf ppf "@[(%a@ %a@ %a)@]"
      (format_tree format_elt) left
      format_elt root
      (format_tree format_elt) right

let format_int_tree = format_tree Format.pp_print_int

(* #install_printer format_int_tree *)


let rec range ~from:lower ~upto:upper =
  if lower > upper then []
  else lower :: range ~from:(lower+1) ~upto:upper



module type ListBalancer = sig
  val name : string 
  val balance : 'elt list -> 'elt tree
end


(** Method: dichotomy on an array *)
module DichotomyOnArray : ListBalancer = struct
  
  let name = "Dichotomy on an array"
  
  let rec tree_of_subarray ~from ~upto array =
    if upto < from then Leaf
    else
      let middle = (from + upto) / 2 in
      Node (
        tree_of_subarray ~from ~upto:(middle-1) array,
        Array.get array middle,
        tree_of_subarray ~from:(middle+1) ~upto array
      )
        
  let balance list =
    let array = Array.of_list list in
    tree_of_subarray ~from:0 ~upto:(Array.length array - 1) array

end

(** Method: dichotomy on a list, using list eating. *)
module DichotomyOnList : ListBalancer = struct

  let name = "Dichotomy on a list"
  
  let rec tree_of_list ~how_many list =
    if how_many = 0 then (Leaf,list)
    else
      let middle = (how_many + 1) / 2 in
      let (left_tree, sublist) = tree_of_list ~how_many:(middle-1) list in
      let (right_tree, remains) =
        tree_of_list ~how_many:(how_many - middle) (List.tl sublist)
      in
      (Node (left_tree, List.hd sublist, right_tree), remains)
      

  let balance list =
    list
    |> tree_of_list ~how_many:(List.length list) 
    |> fst

end


(** Method: single-pass with stack of trees *)
module SinglePassStacking : ListBalancer = struct

  let name = "Single pass using a stack of perfect trees"

  let rec push stack (tree2,depth2,elt2) =
    match stack with
    | (tree1,depth1,elt1)::others when depth1 = depth2 ->
      push others (Node (tree1,elt1,tree2), depth1 + 1, elt2)
    | _ -> (tree2,depth2,elt2)::stack

  let combine_stack list =
    List.fold_left 
      (fun tree2 (tree1,depth,root) -> Node (tree1,root,tree2))
      Leaf
      list 

  let balance list =
    list
    |> List.fold_left (fun stack elt -> push stack (Leaf,-1,elt)) []
    |> combine_stack
    
   
end



module IteratedPassGroupByFour : ListBalancer = struct

  let name = "Iterated passes making group of four items and reducing"

  type 'elt item =
    | Elt of 'elt
    | Tree of 'elt tree

  let initialise_alternation list =
    list
    |> List.map (fun elt -> [ Tree Leaf; Elt elt ])
    |> List.flatten
         
  let rec pass = function
    | Tree tree1 :: Elt elt1 :: Tree tree2 :: Elt elt2 :: others ->
      Tree (Node (tree1,elt1,tree2)) :: Elt elt2 :: pass others
    | [ Tree tree1; Elt elt1; Tree tree2 ] ->
      [ Tree (Node (tree1, elt1, tree2)) ]
    | [ Tree tree1; Elt elt1 ] ->
      [ Tree (Node (tree1, elt1,Leaf)) ]
    | [ Tree tree ] as list -> list
    | [] -> []
    | any_other -> assert false


  let rec aggregate = function
    | [ Tree final ] -> final
    | list -> list |> pass |> aggregate

  let balance list =
    list
    |> initialise_alternation
    |> aggregate

end


let module_list =
  [ (module DichotomyOnArray : ListBalancer);
    (module DichotomyOnList : ListBalancer);
    (module SinglePassStacking : ListBalancer);
    (module IteratedPassGroupByFour : ListBalancer)
  ]


(* #use "topfind";; #require "unix";; *)

let test ~count list_length balancer_module =
  let module Balancer = (val balancer_module : ListBalancer) in
  let start_time = Unix.gettimeofday () in 
  let tree = Balancer.balance  (range ~from:1 ~upto:list_length) in
  for i = 2 to count do
    ignore (Balancer.balance  (range ~from:1 ~upto:list_length))
  done;
  let delay = 1000. *. (Unix.gettimeofday () -. start_time) /. float count in
  Printf.printf "\n%s: %fms.\n%!" Balancer.name delay;
  if list_length < 128 then
    Format.printf "%a\n%!" format_int_tree tree
  



let result =
  List.iter (test ~count:100 100) module_list
