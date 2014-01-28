open Latex
open Prelude

let keywords = [
  "let";
  "rec";
  "in";
  "val";
  "fun";
  "function";
  "type";
  "and";
  "match";
  "try";
  "with";
  "module";
  "struct";
  "sig";
  "begin";
  "end";
]

let hspace_ s = command "hspace*" [T, latex_of_size s] T
let symbols = [
  "->", rightarrow;
  "::", texttt(text":"^^hspace_ (`Em (-0.25))^^text":");
]

let verbatim_code x = texttt (Verbatim.verbatim (Verbatim.trim ['\n'] x))

let verbatim_keywords =
  Latex.Verbatim.keywords ~apply: (fun _ -> texttt (symbolc '_')) ["_"]

let ocaml_code_base x =
  Latex.Verbatim.pseudocode
    ~trim: (fun s -> s)
    ~id_apply: (fun i -> textsf (verbatim_keywords (to_string i)))
    ~kw_apply: (fun x -> textbf (textsf x))
    ~rem_apply: (fun s -> texttt (Latex.Verbatim.verbatim s))
    ~keywords
    ~symbols
    ~underscore: (Str.regexp "__")
    x

let dquote = String.make 1 '"'

let to_greek = function
  | "'a" -> upalpha
  | "'b" -> upbeta
  | "'c" -> upgamma
  | "'d" -> updelta
  | "'e" -> upepsilon
  | "'r" -> uprho
  | "'s" -> upsigma
  | "'odd" -> upomega
  | "'even" -> upeta
  | tp -> failwith ("unsupported ocaml type: "^tp)

let ocaml_code x =
  Melt.Verbatim.regexps [
    Str.regexp "[\n]\\([ ]*[\n]\\)+",
      (fun _ -> Latex.newline_size (`Baselineskip 0.5));
    Str.regexp "[\n]",
      (fun _ -> Latex.newline);
    Str.regexp "^[ ]+", (** indentation *)
      (fun s -> Latex.Verbatim.verbatim s);
    Str.regexp "[ ]+", (** other spaces *)
      (fun _ -> text"~");
    Str.regexp "\034\\([\\]\034\\|[^\034]\\)*\034",
      (fun s -> texttt (Latex.Verbatim.verbatim s));
    Str.regexp "(\\*\\([^*]\\|\\*[^)]\\)*\\*)",
      (fun s -> textit (text s));
    Str.regexp "'[a-z]+",
       to_greek;
    Str.regexp "|",
       (fun _ -> hspace_ (`Em 0.1)^^rule_ ~lift:(`Ex (-0.6)) (`Sp 1.) (`Baselineskip 1.)^^hspace_ (`Em 0.2));
  ] ocaml_code_base (Melt.Verbatim.trim ['\n'] x)
