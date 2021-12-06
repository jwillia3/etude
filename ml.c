#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define new(t,...) memcpy(malloc(sizeof(t)), &(t){__VA_ARGS__}, sizeof(t))

typedef struct {int n; char *s;} String;
typedef struct {char *fn; int ln;} Pos;
struct infix {char *id; int lhs, rhs; struct infix *next;};

typedef struct value {
    enum {BOOLE,INT,STRING,TUPLE,LIST,FN} type;
    union {
        int     i;
        String  *s;
        struct tuple *tup;
        struct lst *lst;
        struct fn {struct expr *e; struct values *vars;} *fn;
    };
} value;
struct lst {value hd, tl;};
struct tuple {int n; value xs[];};
typedef struct values {value x; struct values *next;} values;

enum token {
    TEOF,TINT,TSTRING,TLP,TRP,TLB,TRB,TCOMMA,TSEMI,TID,TEQUAL,
    TIF,TTHEN,TELSE,TCASE,TBAR,TARROW,TLET,TREC,TAND,TIN,TFN,
    TTRUE,TFALSE
};
char *tokens[] = {
    "end of file","int","string","(",")","[","]",",",";","id",
    "=","if","then","else","case","|","->","let","rec","and",
    "in","fn","true","false",0
};
enum op {
    OISBOOL,OISINT,OISSTR,OISCONS,OISLIST,OISTUP,OISFN,
    OLEN,OTLEN,OHD,OTL,OPRINT,
    OBINARY,
    OEQ,ONE,OLT,OGT,OLE,OGE,OCONS,OADD,OSUB,OMUL,ODIV,OREM,OIDX,OTIDX,
    OTOTAL
};
char *ops[] = {
    "isbool","isint","isstring","iscons","islist","istuple","isfn",
    "length","tuplelength","hd","tl","print",
    "",
    "==","<>","<",">","<=",">=",":","+","-","*","/","rem","@","@*",0
};
value opvals[OTOTAL];

typedef struct expr Expr;
struct expr {
    enum {
        ELIT,EID,ETUPLE,ELIST,EFN,EAPP,EBIN,EUN,EIF,ECASE,ELET,
        ESEQ,ECRASH
    } form;
    Pos     pos;
    union {
        value x;
        struct {char *id; int index;};
        struct {int n; Expr **es;};
        struct {Expr *lhs, *rhs; enum op op;};
        struct {Expr *cond, *yes, *no;};
        struct {Expr *sub; struct rule *cases;};
        struct {bool rec; struct rule *defs; Expr *in;};
        Expr *crash;
    };
};
struct rule {Expr *lhs, *rhs; struct rule *next;};

typedef struct varenv {char *id; struct varenv *next;} varenv;

char            source[65536];
char            *src;
enum token      token;
bool            peeked;
int             tokint;
char            tokbuf[sizeof source];
String          *toktxt;
String          *interns;
int             ninterns;
Pos             srcpos;
struct infix    *infixes;
const value     nil = {LIST, .lst=0};
const value     unit = {TUPLE, .tup=&(struct tuple) {0}};

#define Expr(f,p,...) new(Expr, .form=(f), .pos=(p), __VA_ARGS__)
Expr *expr();
Expr *aexpr(bool required);
void pr(char *msg, ...);

String *intern(char *txt, int n) {
    if (n < 0) n = strlen(txt);

    for (String *i = interns; i < interns + ninterns; i++)
        if (i->n == n && !memcmp(i->s, txt, n)) return i;

    String str = (String) {.n=n, .s=malloc(n + 1)};
    memcpy(str.s, txt, n);
    str.s[n] = 0;

    interns = realloc(interns, (ninterns + 1) * sizeof *interns);
    interns[ninterns] = str;
    return interns + ninterns++;
}

/*

    Value Manipulation Functions

*/
bool isnil(value x) { return x.type == LIST && !x.lst; }
bool iscons(value x) { return x.type == LIST && x.lst; }
bool isbool(value x) { return x.type == BOOLE; }
bool isint(value x) { return x.type == INT; }
bool isstring(value x) { return x.type == STRING; }
bool islist(value x) { return x.type == LIST; }
bool istuple(value x) { return x.type == TUPLE; }
bool isfn(value x) { return x.type == FN; }
value boole(bool x) { return (value) {BOOLE, .i=x}; }
value integer(int i) { return (value) {INT, .i=i}; }
value string(String *s) { return (value) {STRING, .s=s}; }
value newtuple(int n) {
    struct tuple *tup = malloc(sizeof *tup + n * sizeof *tup->xs);
    tup->n = n;
    return (value) {TUPLE, .tup=tup};
}
value cons(value hd, value tl) {
    return (value) {LIST, .lst=new(struct lst, hd, tl)};
}
value fn(Expr *e, values *vars) {
    return (value) {FN, .fn=new(struct fn, e, vars)};
}

bool equal(value x, value y) {
    if (x.type != y.type) return false;

    switch (x.type) {
    case BOOLE:     return x.i == y.i;
    case INT:       return x.i == y.i;
    case STRING:    return x.s == y.s ||
                        x.s->n == y.s->n && !memcmp(x.s->s, y.s->s, x.s->n);
    case TUPLE:     if (x.tup->n != y.tup->n) return false;
                    for (int i = 0; i < x.tup->n; i++)
                        if (!equal(x.tup->xs[i], y.tup->xs[i])) return false;
                    return true;
    case LIST:      for ( ; iscons(x) && iscons(y); x=x.lst->tl, y=y.lst->tl)
                        if (!equal(x.lst->hd, y.lst->hd));
                    return isnil(x) && isnil(y);
    case FN:        return x.fn == y.fn;
    }
    return false;
}


void printexpr(Expr *e) {
    switch (e->form) {
    case ELIT:      pr("%v", e->x); break;
    case EID:       pr("%s", e->id); break;
    case ETUPLE:
    case ELIST:     pr(e->form == ETUPLE? "(": "[");
                    for (int i = 0; i < e->n; i++)
                        pr("%s%e", i? ", ": "", e->es[i]);
                    pr(e->form == ETUPLE? ")": "]");
                    break;
    case EFN:       pr("(fn %e->%e)", e->lhs, e->rhs); break;
    case EUN:       pr("(%s %e)", ops[e->op], e->rhs); break;
    case EBIN:      pr("(%e %s %e)", e->lhs, ops[e->op], e->rhs); break;
    case EAPP:      pr("(%e %e)", e->lhs, e->rhs); break;
    case EIF:       pr("(if %e then %e else %e)", e->cond, e->yes, e->no);break;
    case ECASE:     pr("(case %e", e->sub);
                    for (struct rule *i = e->cases; i; i = i->next)
                        pr(" | %e->%e", i->lhs, i->rhs);
                    pr(")");
                    break;
    case ELET:      pr("let %s", e->rec? "rec ": "");
                    for (struct rule *i = e->defs; i; i = i->next)
                        pr("%e=%e %s", i->lhs, i->rhs, i->next? "and ": "");
                    pr("in %e", e->in);
                    break;
    case ESEQ:      pr("(%e; %e)", e->lhs, e->rhs); break;
    case ECRASH:    pr("(*CRASH*)"); break;
    }
}

void printvalue(value x, bool decorate) {
    switch (x.type) {
    case BOOLE:     pr(x.i? "true": "false"); break;
    case INT:       pr("%d", x.i); break;
    case STRING:    if (decorate) {
                        pr("\"");
                        for (int i = 0; i < x.s->n; i++)
                            if (x.s->s[i] == '\n') pr("\\n");
                            else if (x.s->s[i] == '\t') pr("\\t");
                            else if (x.s->s[i] == '\"') pr("\\\"");
                            else pr("%c", x.s->s[i]);
                        pr("\"");
                    } else pr("%s", x.s->s);
                    break;
    case TUPLE:     pr("(");
                    for (int i = 0; i < x.tup->n; i++)
                        pr("%s%v", i? ", ": "", x.tup->xs[i]);
                    pr(")");
                    break;
    case LIST:      pr("[");
                    for (value i = x; !isnil(i); i = i.lst->tl)
                        pr("%v%s", i.lst->hd, isnil(i.lst->tl)? "": ", ");
                    pr("]");
                    break;
    case FN:        pr("#fn"); break;
    }

}

void vpr(char *msg, va_list ap) {
    char *msg2;
    for (char *s = msg; *s; s++)
        if (*s != '%') putchar(*s);
        else switch (*++s) {
        case 'c': putchar(va_arg(ap, int)); break;
        case 'd': printf("%d", va_arg(ap, int)); break;
        case 's': printf("%s", va_arg(ap, char *)); break;
        case 'e': printexpr(va_arg(ap, Expr *)); break;
        case 'v': printvalue(va_arg(ap, value), true); break;
        case 'V': printvalue(va_arg(ap, value), false); break;
        case '!': putchar('\n'); exit(1); break;
        case '*': msg2 = va_arg(ap, char *);
                    vpr(msg2, *va_arg(ap, va_list *));
                    break;
        }
}

void pr(char *msg, ...) {
    va_list ap; va_start(ap, msg);
    vpr(msg, ap);
    va_end(ap);
}

void syntax(char *msg, ...) {
    va_list ap; va_start(ap, msg);
    pr("ml: error %s:%d: %* before %s%!",
        srcpos.fn, srcpos.ln, msg, &ap, tokens[token]);
}

void *semantic(Expr *e, char *msg, ...) {
    va_list ap; va_start(ap, msg);
    pr("ml: error %s:%d: %*\nexpr: %e%!", e->pos.fn, e->pos.ln, msg, &ap, e);
    return 0;
}

void opensrc(char *fn) {
    srcpos = (Pos) {strdup(fn), 1};
    src = source;
    peeked = false;

    FILE *file = fopen(fn, "rb");
    if (!file) syntax("cannot open file");
    source[fread(source, 1, sizeof source, file)] = 0;
    fclose(file);
}

enum token next() {
    char *t = tokbuf;
    char *opchr = "!%&$*+-/:<=>?@~`^|";

    if (peeked) return peeked = false, token;

    while (isspace(*src) || *src == '#')
        if (*src == '#') while (*src && *src != '\n') src++;
        else if (*src == '\n') src++, srcpos.ln++;
        else src++;

    if (!*src) return token = 0;
    for (int i = TLP; i <= TSEMI; i++)
        if (*src == tokens[i][0]) return src++, token = i;
    if (isdigit(src[*src == '-']))
        return tokint = strtol(src, &src, 10), token = TINT;
    if (*src == '"')
        for (src++; ; src++)
            if (!*src || *src == '\n') syntax("unclosed string");
            else if (*src == '"') {
                src++;
                return toktxt = intern(tokbuf, t - tokbuf), token = TSTRING;
            } else if (*src != '\\') *t++ = *src;
            else switch (*++src) {
            case 'n': *t++ = '\n'; break;
            case 't': *t++ = '\t'; break;
            default: *t++ = *src;
            }

    while (isalnum(*src) || *src == '_' || *src == '\'') *t++ = *src++;
    if (t == tokbuf) while (*src && strchr(opchr, *src)) *t++ = *src++;
    if (t == tokbuf) syntax("not a token: %c", *src);
    toktxt = intern(tokbuf, t - tokbuf);

    for (char **i = tokens; *i; i++)
        if (*i == toktxt->s) return token = i - tokens;
    return token = TID;
}

bool peek(enum token t) { peeked = next(); return token == t; }
bool want(enum token t) { peeked = next() != t; return !peeked; }
void need(enum token t) { if (!want(t)) syntax("need %s", tokens[t]); }

/*

    Parsing Expressions

*/

Expr *crash(Expr *e) { return Expr(ECRASH, e->pos, .crash=e); }
Expr *lit(Pos pos, value x) { return Expr(ELIT, pos, .x=x); }
Expr *app(Expr *f, Expr *x) { return Expr(EAPP, f->pos, .lhs=f, .rhs=x); }
Expr *binary(Expr *lhs, enum op op, Expr *rhs) {
    return Expr(EBIN, lhs->pos, .lhs=lhs, .rhs=rhs, .op=op);
}
Expr *unary(enum op op, Expr *rhs) {
    return Expr(EUN, rhs->pos, .rhs=rhs, .op=op);
}
Expr *var(Pos pos, char *id, int index) {
    return Expr(EID, pos, .id=intern(id, -1)->s, .index=index);
}
Expr *uniquevar(Pos pos) {
    static int count;
    char buf[16];
    sprintf(buf, "__%d", ++count);
    return var(pos, buf, -1);
}
Expr *_if(Expr *cond, Expr *yes, Expr *no) {
    return Expr(EIF, cond->pos, .cond=cond, .yes=yes, .no=no);
}
Expr *let(Pos pos, char *id, Expr *x, Expr *in) {
    struct rule *defs = new(struct rule, .lhs=var(pos, id,-1), .rhs=x, .next=0);
    return Expr(ELET, pos, .rec=false, .defs=defs, .in=in);
}
bool istrivial(Expr *e) {
    switch (e->form) {
    case ELIT: case EID: case ETUPLE: case ELIST: case EFN:
        return true;
    case EAPP: case EBIN: case EUN: case EIF: case ECASE:
    case ELET: case ESEQ: case ECRASH:
        return false;
    }
    return false;
}

struct infix *findinfix() {
    if (peek(TID))
        for (struct infix *i = infixes; i; i = i->next)
            if (i->id == toktxt->s) return i;
    return 0;
}

Expr *funexpr(enum token separator) {
    if (want(separator)) return expr();
    Expr *lhs = aexpr(true);
    Expr *rhs = funexpr(separator);
    return Expr(EFN, lhs->pos, .lhs=lhs, .rhs=rhs);
}

Expr *aexpr(bool required) {
    Pos pos = srcpos;
    if (!required && findinfix()) return 0; // Avoid eating operator as an arg.
    if (want(TINT))     return lit(pos, integer(tokint));
    if (want(TSTRING))  return lit(pos, string(toktxt));
    if (want(TTRUE))    return lit(pos, boole(true));
    if (want(TFALSE))   return lit(pos, boole(false));
    if (want(TID))      return var(pos, toktxt->s, -1);
    if (want(TLP) || want(TLB)) {
        enum token end = token == TLP? TRP: TRB;
        int n = 0;
        Expr **es = 0;
        do {
            if (peek(end)) break;
            es = realloc(es, (n + 1) * sizeof *es);
            es[n++] = expr();
        } while (want(TCOMMA));
        need(end);

        if (n == 0) return lit(pos, end == TRP? unit: nil);
        if (end == TRP && n == 1) return es[0];
        return Expr(end == TRP? ETUPLE: ELIST, pos, .n=n, .es=es);
    }
    if (want(TFN)) return funexpr(TARROW);
    if (required) syntax("need expression");
    return 0;
}

Expr *iexpr(int level) {
    if (level == 11) {
        Expr *lhs = aexpr(true);
        Expr *rhs;
        while ((rhs = aexpr(false))) // Function application
            lhs = app(lhs, rhs);
        return lhs;
    }

    Expr *lhs = iexpr(level + 1);
    struct infix *op;
    while ((op = findinfix()) && op->lhs == level) { // Binary operator
        next();
        Expr *rhs = iexpr(op->rhs);
        lhs = app(app(var(lhs->pos, op->id, -1), lhs), rhs);
    }
    return lhs;
}

struct rule *caserules() {
    if (!want(TBAR)) return 0;
    Expr *lhs = expr();
    Expr *rhs = (want(TARROW), expr());
    struct rule *next = caserules();
    return new(struct rule, lhs, rhs, next);
}

struct rule *letdefs() {
    Expr *lhs = aexpr(true);
    Expr *rhs = funexpr(TEQUAL);
    struct rule *next = want(TAND)? letdefs(): 0;
    return new(struct rule, lhs, rhs, next);
}

Expr *cexpr() {
    Pos pos = srcpos;
    if (want(TIF)) {
        Expr *cond = expr();
        Expr *yes = (need(TTHEN), expr());
        Expr *no = (need(TELSE), expr());
        return _if(cond, yes, no);
    }
    if (want(TCASE)) {
        Expr *sub = expr();
        struct rule *rules = caserules();
        return Expr(ECASE, sub->pos, .sub=sub, .cases=rules);
    }
    if (want(TLET)) {
        bool rec = want(TREC);
        struct rule *defs = (want(TAND), letdefs());
        Expr *in = (need(TIN), expr());
        return Expr(ELET, pos, .rec=rec, .defs=defs, .in=in);
    }
    return iexpr(0);
}

Expr *expr() {
    Expr *e = cexpr();
    return want(TSEMI)? Expr(ESEQ, e->pos, .lhs=e, .rhs=expr()): e;
}


/*

    Expression Transformation
    - Check semantics (variables defined, form correct)
    - Simplify expressions
    - Index variables
    - Avoid modifying existing Expr; create new ones
    - Only xform() should call itself after other functions
      have been called to modify substructures

*/

varenv *find(char *id, varenv *vars, int *index) {
    *index = 0;
    for (varenv *i = vars; i; i = i->next, (*index)++)
        if (i->id == id) return i;
    return 0;
}

int findop(char *id) {
    for (int i = 0; ops[i]; i++) if (ops[i] == id) return i;
    return -1;
}

Expr *xform_app(Expr *e) {
    // Try to directly apply unary.
    if (e->lhs->form == EID) {
        int i = findop(e->lhs->id);
        if (i >= 0 && i < OBINARY)
            return unary(i, e->rhs);
    }

    // Try to directly apply binary.
    if (e->lhs->form == EAPP && e->lhs->lhs->form == EID) {
        int i = findop(e->lhs->lhs->id);
        if (i >= 0 && i > OBINARY)
            return binary(e->lhs->rhs, i, e->rhs);
    }

    return e;
}

Expr *xform_pat(Expr *e, Expr *x, Expr *yes, Expr *no) {
    Expr *tmp;

    switch (e->form) {

    case ELIT:      return _if(binary(e, OEQ, x), yes, no);

    case EID:       return !strcmp("_", e->id) && istrivial(x)
                             ? yes
                             : let(e->pos, e->id, x, yes);

    case ETUPLE:    for (int i = e->n; i-- > 0; ) {
                        Expr *ie = binary(x, OTIDX, lit(x->pos, integer(i)));
                        yes = xform_pat(e->es[i], ie, yes, no);
                    }
                    tmp = binary(unary(OTLEN, x),
                                 OEQ,
                                 lit(e->pos, integer(e->n)));
                    yes = _if(tmp, yes, no);
                    return _if(unary(OISTUP, x), yes, no);

    case ELIST:    for (int i = e->n; i-- > 0; ) {
                        Expr *ie = binary(x, OIDX, lit(x->pos, integer(i)));
                        yes = xform_pat(e->es[i], ie, yes, no);
                    }
                    tmp = binary(unary(OLEN, x),
                                 OEQ,
                                 lit(e->pos, integer(e->n)));
                    yes = _if(tmp, yes, no);
                    return _if(unary(OISCONS, x), yes, no);

    case EBIN:      if (e->op == OCONS) {
                        yes = xform_pat(e->rhs, unary(OTL, x), yes, no);
                        yes = xform_pat(e->lhs, unary(OHD, x), yes, no);
                        return _if(unary(OISCONS, x), yes, no);
                    }
                    goto bad;

    case EAPP:      tmp = xform_app(e);
                    if (tmp->form == EAPP) goto bad;
                    return xform_pat(tmp, x, yes, no);

    default:        bad: return semantic(e, "illegal pattern");
    }
}

Expr *xform_cases(Expr *x, struct rule *r, Expr *no) {
    return r? xform_pat(r->lhs, x, r->rhs, xform_cases(x, r->next, no)): no;
}

Expr *xform_defs(struct rule *r, Expr *yes, Expr *no) {
    return r? xform_pat(r->lhs, r->rhs, xform_defs(r->next, yes, no), no): yes;
}

Expr *xform(Expr *e, varenv *vars) {
    varenv  *v;
    Expr    *tmp;
    int     index;

    switch (e->form) {
    case ELIT:      return e;

    case EID:       // Find de Bruijn index for variable.
                    if ((v = find(e->id, vars, &index))) {
                        // Create new reference with correct index.
                        // DO NOT UPDATE, EVAR objects can be shared.
                        // (e.g. a temp created for a case expression)
                        return var(e->pos, e->id, index);
                    }

                    // Reverence static primitive, if so
                    if ((index = findop(e->id)) >= 0)
                        return lit(e->pos, opvals[index]);

                    // Otherwise, the variable is undefined.
                    return semantic(e, "undefined symbol");

    case ETUPLE:
    case ELIST:     for (int i = 0; i < e->n; i++)
                        e->es[i] = xform(e->es[i], vars);
                    return e;

    case EFN:       // Simple one-variable function.
                    // Check r.h.s. with parameter added to variables.
                    if (e->lhs->form == EID) {
                        e->rhs = xform(e->rhs, new(varenv, e->lhs->id, vars));
                        return e;
                    }
                    // Otherwise, introduce named parameter and xform pattern.
                    else {
                        Expr *uid = uniquevar(e->lhs->pos);
                        Expr *body = xform_pat(e->lhs, uid, e->rhs, crash(e));
                        e = Expr(EFN, e->pos, .lhs=uid, .rhs=body);
                        return xform(e, vars);
                    }

    case EUN:       e->rhs = xform(e->rhs, vars);
                    return e;

    case ESEQ:
    case EBIN:      e->lhs = xform(e->lhs, vars);
                    e->rhs = xform(e->rhs, vars);
                    return e;

    case EAPP:      tmp = xform_app(e);
                    if (tmp->form == EAPP) {
                        e->lhs = xform(e->lhs, vars);
                        e->rhs = xform(e->rhs, vars);
                        return e;
                    } else
                        return xform(e, vars);

    case EIF:       e->cond = xform(e->cond, vars);
                    e->yes = xform(e->yes, vars);
                    e->no = xform(e->no, vars);
                    return e;

    case ECASE:     if (e->sub->form == EID) {
                        e = xform_cases(e->sub, e->cases, crash(e));
                        return xform(e, vars);
                    } else {
                        // Create a temporary to hold the subject value.
                        Expr *sub = uniquevar(e->sub->pos);
                        Expr *in = xform_cases(sub, e->cases, crash(e));
                        Expr *out = let(sub->pos, sub->id, e->sub, in);
                        return xform(out, vars);
                    }

    case ELET:      if (e->rec) {
                        // Define all functions first.
                        // All definitions will have IDs on the l.h.s.
                        for (struct rule *i = e->defs; i; i = i->next) {
                            if (i->lhs->form != EID)
                                return semantic(i->lhs, "l.h.s. must be var");
                            if (i->rhs->form != EFN)
                                return semantic(i->rhs, "r.h.s. must be fn");
                            vars = new(varenv, i->lhs->id, vars);
                        }

                        for (struct rule *i = e->defs; i; i = i->next)
                            i->rhs = xform(i->rhs, vars);

                        e->in = xform(e->in, vars);
                        return e;
                    }
                    // Single variable let definition (`let x = ... in ...`).
                    // Every non-recursive let will end up in this form.
                    else if (!e->defs->next && e->defs->lhs->form == EID) {
                        varenv *newvars = new(varenv, e->defs->lhs->id, vars);
                        e->defs->rhs = xform(e->defs->rhs, vars);
                        e->in = xform(e->in, newvars);
                        return e;
                    }
                    // Break down multiple and/or pattern defs into singles.
                    // Reprocess once broken down.
                    else {
                        e = xform_defs(e->defs, e->in, crash(e));
                        return xform(e, vars);
                    }

    case ECRASH:    return e;
    default:        return semantic(e, "UNTRANSFORMED");
    }
}

void addinfix(int lhs, int rhs, char **ids) {
    for (char **i = ids; *i; i++)
        infixes = new(struct infix, intern(*i, -1)->s, lhs, rhs, infixes);
}

value eval_op(Expr *e, value x, value y) {
    int n;
    value i;

    switch (e->op) {

    case OLEN:
        if (!islist(x)) semantic(e, "NOT_LIST %v", x);
        for (n = 0; !isnil(x); x = x.lst->tl) n++;
        return integer(n);

    case OTLEN:
        if (!istuple(x)) semantic(e, "NOT_TUPLE %v", x);
        return integer(x.tup->n);

    case OHD:
        if (!iscons(x)) semantic(e, "HD_NOT_LIST %v", x);
        return x.lst->hd;

    case OTL:
        if (!iscons(x)) semantic(e, "TL_NOT_LIST %v", x);
        return x.lst->tl;

    case OPRINT:
        pr("%V", x);
        return x;

    case OISBOOL:   return boole(isbool(x));
    case OISINT:    return boole(isint(x));
    case OISSTR:    return boole(isstring(x));
    case OISCONS:   return boole(iscons(x));
    case OISLIST:   return boole(islist(x));
    case OISTUP:    return boole(istuple(x));
    case OISFN:     return boole(isfn(x));

    case OCONS:
        if (!islist(y)) semantic(e, "NON_LIST_TAIL %v", y);
        return cons(x, y);

    case OIDX:
        if (!islist(x)) semantic(e, "NON_LIST_BASE %v", x);
        if (!isint(y)) semantic(e, "NON_INTEGER_INDEX %v", y);
        for (i = x, n = y.i; n-- > 0 && iscons(i); ) i = i.lst->tl;
        if (isnil(i)) semantic(e, "BOUNDS %v @ %v", x, y);
        return i.lst->hd;

    case OTIDX:
        if (!istuple(x)) semantic(e, "NON_TUPLE_BASE %v", x);
        if (!isint(y)) semantic(e, "NON_INTEGER_INDEX %v", y);
        if (y.i < 0 || y.i >= x.tup->n) semantic(e, "BOUNDS %v @* %v", x, y);
        return x.tup->xs[y.i];

    case OEQ:       return boole(equal(x, y));
    case ONE:       return boole(!equal(x, y));

    case OLT: case OGT: case OLE: case OGE: case OADD: case OSUB:
    case OMUL: case ODIV: case OREM:

        if (!isint(x) || !isint(y))
            semantic(e, "NON_INTEGER %v %s %v", x, y);

        switch (e->op) {
        case OLT:   return boole(x.i < y.i);
        case OGT:   return boole(x.i > y.i);
        case OLE:   return boole(x.i <= y.i);
        case OGE:   return boole(x.i >= y.i);
        case OADD:  return integer(x.i + y.i);
        case OSUB:  return integer(x.i - y.i);
        case OMUL:  return integer(x.i - y.i);
        case ODIV:  return integer(x.i / y.i);
        case OREM:  return integer(x.i % y.i);
        default:    return semantic(e, "UNEVALUATED_OP"), unit;
        }


    default:    return semantic(e, "UNEVALUATED_OP"), unit;
    }
}

value eval(Expr *e, values *vars) {
    value   x, y, *ptr;

    top:
    switch (e->form) {
    case ELIT:      return e->x;

    case EID:       for (int i = e->index; i-- > 0 && vars; ) vars = vars->next;
                    if (!vars || e->index<0) semantic(e, "MISTAKEN_INDEX %d", e->index);
                    return vars->x;

    case ETUPLE:    x = newtuple(e->n);
                    for (int i = 0; i < e->n; i++)
                        x.tup->xs[i] = eval(e->es[i], vars);
                    return x;

    case ELIST:     x = nil;
                    ptr = &x;
                    for (int i = 0; i < e->n; i++) {
                        *ptr = cons(eval(e->es[i], vars), nil);
                        ptr = &ptr->lst->tl;
                    }
                    return x;

    case EFN:       return fn(e->rhs, vars);

    case EAPP:      x = eval(e->lhs, vars);
                    if (x.type != FN) semantic(e, "NON_FUNCTION %v", x);
                    y = eval(e->rhs, vars);
                    vars = new(values, y, x.fn->vars);
                    e = x.fn->e;
                    goto top;

    case EBIN:      x = eval(e->lhs, vars);
                    y = eval(e->rhs, vars);
                    return eval_op(e, x, y);

    case EUN:       return eval_op(e, eval(e->rhs, vars), unit);

    case EIF:       x = eval(e->cond, vars);
                    if (!isbool(x)) semantic(e, "NON_BOOL %v", x);
                    e = x.i? e->yes: e->no;
                    goto top;

    case ELET:      if (e->rec) {
                        values *bottom = vars;
                        for (struct rule *i = e->defs; i; i = i->next)
                            vars = new(values, eval(i->rhs, vars), vars);
                        for (values *i = vars; i != bottom; i = i->next)
                            i->x.fn->vars = vars;
                        e = e->in;
                        goto top;
                    } else {
                        // All lets are single-variable now.
                        x = eval(e->defs->rhs, vars);
                        vars = new(values, x, vars);
                        e = e->in;
                        goto top;
                    }

    case ECRASH:    return semantic(e->crash, "NO_MATCH"), unit;

    case ESEQ:      eval(e->lhs, vars);
                    e = e->rhs;
                    goto top;

    case ECASE:     // does not exist
    default:        return semantic(e, "UNEVALUATED"), unit;
    }
}

int main(int argc, char **argv) {
    for (char **i = tokens; *i; i++) *i = intern(*i, -1)->s;
    for (char **i = ops; *i; i++) *i = intern(*i, -1)->s;

    Pos no = {"(builtin)", 0};
    char *p1 = intern("x", -1)->s;
    char *p2 = intern("y", -1)->s;
    for (int i = 0; i < OBINARY; i++)
        opvals[i] = fn(unary(i, var(no, p1, 0)), 0);
    for (int i = OBINARY + 1; ops[i]; i++) {
        Expr *body = binary(var(no, p1, 1), i, var(no, p2, 0));
        Expr *inner = Expr(EFN, no, .lhs=var(no, p1, -1), .rhs=body);
        opvals[i] = fn(inner, 0);
    }

    addinfix(6, 7, (char*[]){"+","-","*","/","rem",0});
    addinfix(5, 6, (char*[]){"@",0});
    addinfix(5, 5, (char*[]){":",0});
    addinfix(4, 5, (char*[]){"==","<>","<",">","<=",">=",0});

    for (argv++; *argv; argv++) {
        opensrc(*argv);

        while (!peek(TEOF)) {
            Expr *e = expr();
            // pr("# %e\n", e);
            e = xform(e, 0);
            // pr("# %e\n", e);
            value x = eval(e, 0);
            pr("> %v\n", x);
        }
    }
}
