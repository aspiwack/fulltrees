open Latex
open Prelude

let verbatim_code x = texttt (Verbatim.verbatim (Verbatim.trim ['\n'] x))

let verbatim_keywords =
  Latex.Verbatim.keywords ~apply: (fun _ -> texttt (symbolc '_')) ["_"]

let ocaml_code_base x =
  Latex.Verbatim.pseudocode
    ~trim: (fun s -> s)
    ~id_apply: (fun i -> textsf (verbatim_keywords (to_string i)))
    ~kw_apply: (fun x -> textbf (textsf x))
    ~rem_apply: (fun s -> texttt (Latex.Verbatim.verbatim s))
    ~keywords: ["let"; "in"; "val"; "fun"; "type"; "and";"try";"with"]
    ~symbols: ["->", rightarrow]
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
    Str.regexp "\034\\([\\]\034\\|[^\034]\\)*\034",
      (fun s -> texttt (Latex.Verbatim.verbatim s));
    Str.regexp "(\\*\\([^*]\\|\\*[^)]\\)*\\*)",
      (fun s -> textit (text s));
    Str.regexp "'[a-z]+",
       to_greek
  ] ocaml_code_base (Melt.Verbatim.trim ['\n'] x)
