# let source = readfile "prelude.ml"

let lex src =
  # Return the first index that ok is not ture
  let rec while ok i =
    if i < strlen src && ok (char_at src i) then
      while ok (i + 1)
    else
      i
  in

  let err index msg =
    print "ml: error ";
    print msg;
    print ".\n";
    exit 1
  in

  let rec space i =
    if i < strlen src then
      let c = char_at src i in
      if isspace c then
        space (i + 1)
      else if c == '#' then
        space (while (<> '\n') (i + 1))
      else
        i
    else
      strlen src
  in

  let idchr c = isalnum c || c == '_' || c == '\'' in
  let opchr c = char_in "!$%&*+-./:<=>?@^|~" c in
  let pun c = char_in "()[],;" c in
  let keywords = ["=","if","then","else","case","|","->","let",
                  "rec","and","in","fn","true","false","!"] in
  let idtype txt = if exists (== txt) keywords then touppers txt else "ID" in

  let character i =
    if char_at src i == '\\' then
      case char_at src (i + 1)
      | 'n' -> ('\n', i + 2)
      | 't' -> ('\t', i + 2)
      | c   -> (c, i + 2)
    else
      (char_at src i, i + 1)
  in

  let single i =
    let c = char_at src i in
    if isdigit c || c == '-' && (isdigit $ char_at src (i + 1)) then
      let j = while isdigit (i + 1) in
      ("INT", substring i j src, j)
    else if c == '\'' then
      let (txt, j) = character (i + 1) in
      if char_at src j <> '\'' then
        err j "unclosed char"
      else
        ("CHAR", txt, j + 2)
    else if c == '"' then
      let rec do i out =
        if i == strlen src || char_at src i == '\n' then
          err i "unclosed string"
        else if char_at src i == '"' then
          ("STRING", implode $ reverse out, i + 1)
        else
          let (c, i') = character i in
          do i' (c:out)
      in do (i + 1) []
    else if idchr c then
      let j = while idchr i in
      let id = substring i j src in
      (idtype id, id, j)
    else if opchr c then
      let j = while opchr i in
      let id = substring i j src in
      (idtype id, id, j)
    else if pun c then
      let txt = substring i (i + 1) src in
      (txt, txt, i + 1)
    else
      err i ("bad token: " ^ (char_to_string c))
  in

  let rec all i out =
    let i = space i in
    if i < strlen src then
      let (type, text, j) = single i in
      all j ((type, text):out)
    else
      reverse out
  in

  all 0 []

let _ = app pr $ lex (readfile "prelude.ml")
