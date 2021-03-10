#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
pynetree: A light-weight parsing toolkit written in pure Python.
original source: https://github.com/phorward/pynetree
modified via fork: https://github.com/hennadii-demchenko/pynetree
"""
import re
from typing import Union


class GoalSymbolNotDefined(Exception):
    def __init__(self):
        super(GoalSymbolNotDefined, self).__init__(
            "No goal symbol defined in provided grammar")


class SymbolNotFoundError(Exception):
    def __init__(self, name):
        super(SymbolNotFoundError, self).__init__(
            "Symbol not found: '%s'" % name)


class MultipleDefinitionError(Exception):
    def __init__(self, name):
        super(MultipleDefinitionError, self).__init__(
            "Multiple definition of: '%s'" % name)


class ParseError(Exception):
    def __init__(self, s, offset):
        row = s.count("\n", 0, offset) + 1
        col = s.rfind("\n", 0, offset)
        col = (offset + 1) if col < 1 else offset - col

        super(ParseError, self).__init__(
            "Parse error at line %d, column %d: >%s<" % (row, col, s[offset:]))

        self.offset = offset
        self.line = row
        self.column = col


class Node(object):
    """
    This is an AST node.
    """

    def __init__(self, symbol=None, emit=None, match=None, rule=None, children=None):
        self.symbol = symbol
        self.emit = emit
        self.rule = rule
        self.key = self.symbol if self.rule is None \
            else (self.symbol, self.rule)

        self.match = match
        self.children = children or []

    def __str__(self):
        s = self.emit or self.symbol or ""

        if self.rule is not None:
            s += "[%d]" % self.rule

        if not self.children and self.match is not None:
            s += " (%s)" % self.match

        return s

    def check(self, symbol):
        return self.symbol == symbol

    def contains(self, symbol):
        return bool(self.select(symbol, 0))

    def select(self, symbol, idx=-1):
        """
        Select children by symbol from the current node.

        :param symbol: Symbol to be matched.
        :param idx: The desired index of the symbol.
        :return: If idx is < 0, the function returns a list of children matching symbol,
        else it returns the child at position `idx` that matches `symbol`.
        It returns None if there is no child.
        """
        if idx < 0:
            return [child for child in self.children if child.symbol == symbol]

        for child in self.children:
            if child.symbol == symbol:
                if idx == 0:
                    return child

                idx -= 1

        return None

    def dump(self, level=0):
        if self.symbol or self.emit:
            print("%s%s" % (level * " ", str(self)))
            level += 1

        for child in self.children:
            child.dump(level)


class Parser(object):
    """
    The main parser class that implements a pynetree parser.

    The class provides functions for defining the grammar,
    parsing input, dumping and traversing the resulting parse
    tree or abstract syntax tree.
    """
    AUTOTOKNAME = "T$%03d"

    def __init__(self, grm):
        """
        Constructs a new pynetree Parser object.

        :param grm: The grammar to be used; This can either be a dictionary of
                    symbols and relating productions, or a string that is
                    expressed in the BNF-styled grammar definition parser.
        :type grm: dict | str
        """
        self.grammar = {}
        self.goal = None
        self.tokens = {}
        self.ignores = []
        self.emits = {}

        def unique_name(n_):
            """
            Generates a unique symbol name from ``n``, by adding
            single-quotation characters to the end of ``n`` until
            no symbol with such a name exists in the grammar.
            """
            while n_ in self.tokens.keys():
                n_ += "'"

            while n_ in self.grammar.keys():
                n_ += "'"

            return n_

        def generate_modifier(nonterm_, sym_, mod):
            if mod in ["*", "+"]:
                one_or_more = unique_name(nonterm)
                self.grammar[one_or_more] = [[one_or_more, sym_], [sym_]]
                sym_ = one_or_more

            if mod in ["?", "*"]:
                one_or_none = unique_name(nonterm_)
                self.grammar[one_or_none] = [[sym_], []]
                sym_ = one_or_none

            return sym_

        if isinstance(grm, dict):
            # Rewrite grammar modifiers and goal according provided grammar
            for n, np in grm.items():
                if n.startswith("@"):
                    n = n[1:]
                    self.emits[n] = None

                if n.endswith("$"):
                    if n in self.emits.keys():
                        self.emits[n[:-1]] = self.emits[n]
                        del self.emits[n]

                    n = n[:-1]
                    self.goal = n

                if not np:
                    self.grammar[n] = [""]
                elif not isinstance(np, list):
                    self.grammar[n] = [np]
                else:
                    self.grammar[n] = np[:]

                np = self.grammar[n] = [x.split() for x in self.grammar[n]]

                rnp = []
                for p in np:

                    rp = []
                    for sym in p:
                        if len(sym) > 1 and sym.startswith("@"):
                            sym = sym[1:]
                            self.emits[sym] = None

                        if any([len(sym) > 1 and sym.endswith(x)
                                for x in "*+?"]):
                            sym = generate_modifier(n, sym[:-1], sym[-1:])

                        rp.append(sym)

                    rnp.append(rp)

                self.grammar[n] = rnp
        else:
            # Construct a parser for the BNF input language.
            bnf_parser = Parser({
                "opt_ident": ["IDENT", ""],
                "opt_emit": ["EMIT", ""],

                "inline": ["EMIT opt_ident ( alternation )", "( alternation )"],

                "symbol": ["IDENT", "STRING", "TOKEN", "REGEX", "CCL", "inline"],

                "mod_kleene": "symbol *",
                "mod_positive": "symbol +",
                "mod_optional": "symbol ?",
                "modifier": ["mod_kleene", "mod_positive", "mod_optional", "symbol"],

                "sequence": ["sequence modifier", "modifier"],

                "production": ["sequence", ""],

                "alternation": ["alternation | production", "production"],

                "nontermflag": ["GOAL"],  # fixme sticky
                "nontermflags": ["nontermflags nontermflag", "nontermflag", ""],
                "nontermdef": ["opt_emit IDENT nontermflags : alternation ;"],

                "termsym": ["STRING", "REGEX", "CCL", "IDENT"],
                "termdef": ["opt_emit IDENT termsym ;", "IGNORE termsym ;"],

                "definition": ["nontermdef", "termdef"],
                "definitions": ["definitions definition", "definition"],
                "grammar$": "definitions"})

            bnf_parser.ignore(r"\s+")
            bnf_parser.ignore(r"//[^\n]*\n")
            bnf_parser.ignore(r"/\*([^*]|\*[^/])*\*/")

            bnf_parser.token("IDENT", r"\w+")
            bnf_parser.token("CCL", r"\[[^\]]*\]")
            bnf_parser.token("STRING", r"'[^']*'")
            bnf_parser.token("TOKEN", r'"[^"]*"')
            bnf_parser.token("REGEX", r"/(\\.|[^\\/])*/")

            bnf_parser.token("GOAL", "$", static=True)
            bnf_parser.token("EMIT", "@", static=True)
            bnf_parser.token("IGNORE", r"%(ignore|skip)")

            bnf_parser.emit(["IDENT", "STRING", "TOKEN", "REGEX", "CCL",
                            "GOAL", "EMIT", "IGNORE"])
            bnf_parser.emit(["inline", "mod_kleene", "mod_positive",
                             "mod_optional", "production", "nontermdef",
                             "termdef", "grammar"])

            ast = bnf_parser.parse(grm)
            if not ast:
                raise SyntaxError()

            def build_symbol(nonterm_, symdef) -> str:
                """
                AST traversal function for symbol level in the BNF-grammar.
                """

                if symdef.symbol.startswith("mod_"):
                    sym_ = build_symbol(nonterm_, symdef.children[0])
                    sym_ = generate_modifier(nonterm_, sym_, {
                        "kleene": "*",
                        "positive": "+",
                        "optional": "?"
                    }[symdef.symbol[4:]])

                elif symdef.symbol == "inline":
                    sym_ = unique_name(nonterm_)
                    self.grammar[sym_] = []
                    build_nonterminal(sym_, symdef.select("production"))

                    if symdef.select("EMIT"):
                        ident = symdef.select("IDENT", 0)
                        if ident is not None:
                            self.emit(sym_, ident.match)
                        else:
                            self.emit((nonterm_, len(self.grammar[nonterm_])))

                elif symdef.symbol == "TOKEN":
                    sym_ = symdef.match[1:-1]
                    self.tokens[sym_] = sym_
                    self.emits[sym_] = None
                elif symdef.symbol == "REGEX":
                    sym_ = unique_name(nonterm_.upper())
                    self.token(sym_, symdef.match[1:-1])
                    self.emits[sym_] = None
                elif symdef.symbol == "CCL":
                    sym_ = unique_name(nonterm_.upper())
                    self.token(sym_, symdef.match)
                elif symdef.symbol == "STRING":
                    sym_ = symdef.match[1:-1]

                else:
                    sym_ = symdef.match
                return sym_

            def build_nonterminal(nonterm_, prods):
                """
                AST traversal function for nonterminals in the BNF-grammar.
                """
                for prod in prods:
                    seq = []

                    for s in prod.children:
                        seq.append(build_symbol(nonterm_, s))

                    self.grammar[nonterm_].append(seq)

            # Integrate all non-terminals into the grammar.
            for d in ast.select("nontermdef"):
                sym = d.select("IDENT", 0).match
                self.grammar[sym] = []

            # Now build the grammar
            nonterm = None

            for d in ast.children:
                if d.check("termdef"):
                    term = d.select("IDENT", 0)
                    if term:
                        term = term.match
                    else:
                        term = self.AUTOTOKNAME % (len(self.tokens.keys()) + 1)

                    if d.contains("STRING"):
                        dfn = d.select("STRING", 0).match[1:-1]
                    elif d.contains("REGEX"):
                        dfn = re.compile(d.select("REGEX", 0).match[1:-1])
                    elif d.contains("CCL"):
                        dfn = re.compile(d.select("CCL", 0).match)
                    else:
                        dfn = d.select("IDENT", 1).match

                    if term in self.tokens.keys():
                        raise MultipleDefinitionError(term)

                    self.tokens[term] = dfn

                    if d.select("EMIT"):
                        self.emit(term)
                    elif d.select("IGNORE"):
                        self.ignores.append(term)

                else:  # d == "nontermdef"
                    nonterm = d.select("IDENT", 0).match
                    build_nonterminal(nonterm, d.select("production"))

                    if d.select("EMIT"):
                        self.emit(nonterm)
                    if d.select("GOAL"):
                        self.goal = nonterm

            # Last nonterminal becomes goal, if not set by flags
            if not self.goal and nonterm:
                self.goal = nonterm

        if not self.goal:
            raise GoalSymbolNotDefined()

    # print(self.grammar)
    # print(self.tokens)
    # print(self.emits)

    def token(self, name, token=None, static=False, emit=None):
        """
        Adds a new terminal token ``name`` to the parser.

        :param name: The unique, identifying name of the token to be added.
        :type name: str

        :param token: The token definition that is registered with ``name``.
            If this is a str, and ``static`` is False, it will be interpreted
            as regular expression. If omitted, ``token`` is set to ``name`` as
            static string.
        :type token: str | re | callable

        :param static: If True, ``token`` is directly taken as is, and not
            interpreted as a regex str.

        :param emit: If set, the token is configured to be emitted.
        :type emit: bool | str | callable
        """

        if isinstance(name, list):
            for n in name:
                self.token(n, token=token, static=static)

            return

        if name in self.tokens.keys() or name in self.grammar.keys():
            raise MultipleDefinitionError(name)

        if token:
            if not static and isinstance(token, str):
                token = re.compile(token)
        else:
            token = str(name)

        self.tokens[name] = token

        if emit:
            self.emits[name] = emit if not isinstance(emit, bool) else None

    def ignore(self, token, static=False):
        """
        Adds a new ignore terminal (whitespace) to the parser.

        :param token: The token definition of the whitespace symbol.
            If this is a str, and ``static`` is False, it will be interpreted
            as regular expression.
        :type token: str | re | callable

        :param static: If True, ``token`` is directly taken as is, and not
            interpreted as a regex str.
        """

        name = self.AUTOTOKNAME % len(self.tokens.keys())
        self.token(name, token, static)
        self.ignores.append(name)

    def emit(self, name: Union[str, list, tuple], emit=None):
        """
        Defines which symbols of the grammar shall be emitted in the
        generated, abstract syntax tree (AST).

        :param name: The name of the symbol that shall be emitted.
            Alternatively, a list of symbol names is accepted.
        :type name: str | list

        :param emit: An emit string that is used instead of the symbol
                        name. This can also be a callable, which is
                        called using AST traversal. If omitted, the
                        symbol's name is used as emit.
        """
        if isinstance(name, list):
            for n in name:
                self.emit(n, emit)

            return

        if isinstance(name, tuple):
            testname = name[0]
        else:
            testname = name

        if testname not in self.grammar.keys() and testname not in self.tokens.keys():
            raise SymbolNotFoundError(testname)

        self.emits[name] = emit

    def parse(self, s) -> Node:
        """
        Parse ``s`` with the currently defined grammar.

        This invokes the parser on a given input, and returns the
        abstract syntax tree of this input on success.

        The parser is implemented as a modified packrat parsing algorithm,
        with support of left-recursive grammars.

        :param s: The input string to be parsed.
        :param s: str

        :returns: Abstract syntax tree, None on error.
        :rtype: list | tuple
        """

        class Entry(object):
            def __init__(self, res=None, pos=0):
                self.res = res
                self.pos = pos

        class Lr(object):
            def __init__(self, nterm_, seed=None, head=None):
                self.nterm = nterm_
                self.seed = seed  # The initial parse seed
                self.head = head  # Refers to the head

        class Head(object):
            def __init__(self, nterm_):
                self.nterm = nterm_
                self.involved = []  # nterminals involved into left-recursion
                self.evaluate = []  # subset of involved non-terminals that may
            # be evaluated

        memo = {}
        lrstack = []
        heads = {}

        def apply(nterm_, off_):
            """
            Apply nonterminal ``nterm`` on offset ``off``.
            """

            def scan_token(sym, s_, pos_):
                """
                Scan for a token that was previously defined with token().
                """
                if isinstance(self.tokens[sym], str):
                    if s_.startswith(self.tokens[sym], pos_):
                        return len(self.tokens[sym])

                elif callable(self.tokens[sym]):
                    result = self.tokens[sym](s_, pos_)
                    if result:
                        return result

                else:
                    result = self.tokens[sym].match(s[pos_:])
                    if result and s_.startswith(result.group(0), pos_):
                        return len(result.group(0))

                return -1

            def scan_whitespace(s_, pos_):
                """
                Scan for whitespace that was previously defined by ignore().
                """
                while True:
                    i = 0
                    for sym in self.ignores:
                        result = scan_token(sym, s_, pos_)
                        if result > 0:
                            pos_ += result
                            break

                        i += 1

                    if i == len(self.ignores):
                        break

                return pos_

            def consume(nterm__, off__):
                """
                Try to consume any rule of non-terminal ``nterm``
                starting at offset ``off``.
                """
                # print("consume", nterm, off)
                count = 0
                for rule in self.grammar[nterm__]:
                    sym = None
                    seq = []
                    pos_ = off__

                    for sym in rule:
                        pos_ = scan_whitespace(s, pos_)

                        # Is known terminal?
                        if sym in self.tokens.keys():
                            res_ = scan_token(sym, s, pos_)
                            if res_ <= 0:
                                break

                            if sym in self.emits.keys():
                                seq.append(Node(sym, self.emits[sym],
                                                s[pos_:pos_ + res_]))

                            pos_ += res_

                        # Is unknown terminal?
                        elif sym not in self.grammar.keys():
                            if not s[pos_:].startswith(sym):
                                break

                            pos_ += len(sym)

                        # Is non-terminal?
                        else:
                            res_ = apply(sym, pos_)

                            if res_.res is None:
                                break

                            if sym in self.emits.keys():
                                seq.append(Node(sym, self.emits[sym],
                                                s[pos_:pos_ + res_.pos],
                                                children=res_.res))
                            elif isinstance(res_.res, Node):
                                seq.append(res_.res)
                            elif isinstance(res_.res, list):
                                seq += res_.res

                            pos_ = res_.pos

                        sym = None

                    if not sym:
                        pos_ = scan_whitespace(s, pos_)

                        # Insert production-based node?
                        if (nterm__, count) in self.emits.keys():
                            seq = [Node(
                                nterm__, self.emits[(nterm__, count)], rule=count, children=seq
                            )]

                        return seq, pos_

                    count += 1

                return None, off__

            def lrgrow(entry_, head):
                # print("lrgrow", nterm)
                heads[off_] = head

                while True:
                    pos_ = off_
                    head.evaluate = list(head.involved)

                    res_, pos_ = consume(nterm_, pos_)
                    if res_ is None or pos_ <= entry_.pos:
                        break

                    entry_.res = res_
                    entry_.pos = pos_

                del heads[off_]
                return entry_

            def lrstart(entry_):
                # print("lrstart", nterm)
                lr_ = entry_.res

                if not lr_.head:
                    lr_.head = Head(nterm_)

                for item in reversed(lrstack):
                    if item.head == lr_.head:
                        break

                    item.head = lr_.head
                    lr_.head.involved.append(item.nterm)

            def lranswer(entry_):
                # print("lranswer", nterm_)

                head = entry_.res.head
                if head.nterm != nterm_:
                    return Entry(entry_.res.seed, entry_.pos)

                entry_.res = entry_.res.seed
                if entry_.res is None:
                    return Entry(None, entry_.pos)

                return lrgrow(entry_, head)

            def recall():
                entry_ = memo.get((nterm_, off_))
                head = heads.get(off_)

                if not head:
                    return entry_

                if (not entry_
                        and nterm_ not in [head.nterm] + head.involved):
                    return Entry(None, off_)

                if nterm_ in head.evaluate:
                    head.evaluate.remove(nterm_)
                    entry_.res, entry_.pos = consume(nterm_, off_)

                return entry_

            entry = recall()

            if entry is None:
                lr = Lr(nterm_)
                lrstack.append(lr)

                # mark this a fail to avoid left-recursions
                memo[(nterm_, off_)] = entry = Entry(lr, off_)

                res, pos = consume(nterm_, off_)

                lrstack.pop()

                entry.pos = pos
                if lr.head:
                    lr.seed = res
                    return lranswer(entry)

                entry.res = res

            elif entry.res and isinstance(entry.res, Lr):
                lrstart(entry)
                return Entry(entry.res.seed, entry.pos)

            return entry

        ast = apply(self.goal, 0)
        if not ast or ast.pos < len(s):
            # On parse error, try to find longest match from memo cache
            last = ast.pos if ast else 0

            for (nterm, off) in memo.keys():
                if off > last:
                    last = off

            raise ParseError(s, last)

        if self.goal in self.emits.keys():
            return Node(self.goal, self.emits[self.goal], children=ast.res)

        return Node(children=ast.res)  # Return an empty node with children.

    def traverse(self, node, pre_prefix="pre_", pass_prefix="pass_", post_prefix="post_", *args,
                 **kwargs):
        """
        Generic AST traversal function.

        This function allows to walk over the generated abstract syntax tree created by
        :meth:`pynetree.Parser.parse`
        and calls functions before, by iterating over and after the node are walked.

        :param node: The tree node to print.
        :param pre_prefix: Prefix for pre-processed functions, named prePrefix + symbol.
        :param pass_prefix: Prefix for functions processed by passing though children,
        named passPrefix + symbol.
        :param post_prefix: Prefix for post-processed functions, named postPrefix + symbol.
        :param args: Arguments passed to these functions as *args.
        :param kwargs: Keyword arguments passed to these functions as **kwargs.
        """

        def perform(prefix, loop=None, *args_, **kw):
            if not (node.emit or node.symbol):
                return False

            if loop is not None:
                kw["_loopIndex"] = loop

            for x in range(0, 2):
                if x == 0:
                    fname = "%s%s" % (prefix, node.emit or node.symbol)
                else:
                    if node.rule is None:
                        break

                    fname = "%s%s_%d" % (prefix, node.emit or node.symbol, node.rule)

                if fname and fname in dir(self) and callable(getattr(self, fname)):
                    getattr(self, fname)(node, *args_, **kw)
                    return True

                elif loop is not None:
                    fname += "_%d" % loop

                    if fname and fname in dir(self) and callable(getattr(self, fname)):
                        getattr(self, fname)(node, *args_, **kw)
                        return True

            return False

        # Pre-processing function
        perform(pre_prefix, *args, **kwargs)

        # Run through the children.
        for count, i in enumerate(node.children):
            self.traverse(i, pre_prefix, pass_prefix, post_prefix, *args, **kwargs)

            # Pass-processing function
            perform(pass_prefix, loop=count, *args, **kwargs)

        # Post-processing function
        if not perform(post_prefix, *args, **kwargs):

            # Allow for post-process function in the emit info.
            if node.key and callable(self.emits[node.key]):
                self.emits[node.key](node, *args, **kwargs)

            # Else, just dump the emitting value.
            elif node.key and self.emits[node.key]:
                print(self.emits[node.key])

