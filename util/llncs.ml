open Prelude

(*** Binder for llncs.cls *)

type institution = int

let institutions = Hashtbl.create 8

let new_institution =
  let c = ref 0 in
  fun x ->
    incr c;
    let inst = !c in
    Hashtbl.add institutions inst x;
    inst

let print_institution inst =
  Hashtbl.find institutions inst

type title = {
  title : Latex.t;
  running_title : Latex.t option;
}

type author = {
  name : Latex.t;
  running_name : Latex.t option;
  institution : institution;
  email: Latex.t
}

let title_cmd x = Latex.(command "title" [T,x] T)
let running_title_cmd x = Latex.(command "titlerunning" [T,x] T)
let print_title { title ; running_title } =
  let open Latex in
  match running_title with
  | None -> title_cmd title
  | Some running_title ->
      concat [
        title_cmd title; par;
        running_title_cmd running_title;
      ]

let and_cmd = Latex.text"\\and "
let inst_cmd inst = Latex.(command "inst" [T,inst] T)
let authors_cmd authors = Latex.(command "author" [T,authors] T)
let running_authors_cmd authors = Latex.(command "authorrunning" [T,authors] T)
let institutions_cmd institutions = Latex.(command "institute" [T,institutions] T)
let email_cmd address = Latex.(command "email" [T,address] T)

let rec add_email n inst email lst =
  match lst with
  | [] -> n , [inst,[email]]
  | (a,es)::l' when a==inst -> n , (a,email::es)::l'
  | a::l' ->
      let (n,l'') = add_email (n+1) inst email l' in
      n , a::l''
let add_email inst email rlst =
  let (n,lst') = add_email 1 inst email !rlst in
  rlst := lst';
  n

let push x l =
  l := x::!l
let opt_push x l =
  match x with None -> () | Some x -> push x l

let rec and_list a b l =
  let open Latex in
  match l with
  | [] -> concat [ a ; text" and "; b ]
  | c::l -> concat [ a ; text", "; and_list b c l ]
let and_list l =
  match l with
  | a::b::l -> and_list a b l
  | [a] -> a
  | [] -> Latex.empty

let process_emails emails =
  email_cmd (concat_with_sep (List.rev emails) (Latex.text", "))
let print_authors authors =
  (* spiwack: with an association list, we could fix the order. *)
  let institutions = ref [] in
  let names = ref [] in
  let running_names = ref [] in
  List.iter begin fun author ->
    let inst_pos = add_email author.institution author.email institutions in
    push (author.name,inst_pos) names;
    opt_push author.running_name running_names
  end authors;
  let open Latex in
  let process_names with_inst_num =
    let inst_num inst = if with_inst_num then inst_cmd(latex_of_int inst) else empty in
    List.rev_map (fun (n,inst) -> concat [n;inst_num inst]) !names
  in
  let names =
    match !institutions with
    | [_] -> and_list (process_names false)
    | _ -> and_list (process_names true)
  in
  let running_names =
    match List.rev !running_names with
    | [] -> empty
    | r -> running_authors_cmd (and_list r) ^^ par
  in
  let institutions =
    List.fold_right begin fun (inst,emails) acc ->
      (print_institution inst ^^ newline ^^ process_emails emails) :: acc
    end !institutions []
  in
  let institutions = concat_with_sep institutions and_cmd in
  concat [
    authors_cmd names; par;
    running_names;
    institutions_cmd institutions;
  ]

let abstract_env x =
  Latex.(environment "abstract" (T,x) T)

let document ?(options=[]) ?(prelude=Latex.empty) ?(packages=[]) ~title ~abstract ~authors body =
  let open Latex in
  let options = (A,concat_with_sep options (text",")) in
  concat [
    documentclass ~opt:options (text"llncs"); par;
    require_packages packages;
    required_packages; par;
    prelude; par;
    print_title title; par;
    print_authors authors; par;
    documentmatter (concat_with_sep [
      text"\\maketitle";
      abstract_env abstract;
      body;
    ] (text"\n%\n"));
  ]
