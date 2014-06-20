
let has_some = function
  | None -> false
  | _ -> true

exception IsNone 
let get = function
  | Some x -> x
  | None -> raise IsNone

let map f = function
  | Some x -> Some (f x)
  | None -> None

let default d = function
  | Some x -> x
  | None -> d
  
let cons a l = match a with
  | Some a -> a::l
  | None -> l

let flatten l = 
  List.fold_right cons l []
