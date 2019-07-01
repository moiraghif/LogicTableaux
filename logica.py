import re


ET_CHAR = "∧"
OR_CHAR = "∨"
IF_CHAR = "→"
NOT_CHAR = "¬"

# First order Logic
ALL_CHAR = "∀"
EXISTS_CHAR = "∃"

# Modal Logic
NECESSARY_CHAR = "◻"
POSSIBLE_CHAR = "◇"

# Results
THEOREM_CHAR = "⊢"
NOT_THEOREM_CHAR = "⊬"


def get_all(l):
    "Returns all elements in nested lists"
    o = list()
    for i in l:
        if i:
            o += get_all(i) if isinstance(i, list) else [i]
    return o


def p_new(params):
    if not params:
        return "p1"
    return "p" + str(max(map(lambda p: int(re.search(r"(?<=p)\d+", p).group()),
                             params)) + 1)


class FBF:
    # The Well Formulated Formula, eventually annotated with a sign
    def __str__(self):
        txt = self.sign if self.sign else ""
        if len(self.args) > 1 and self.char:
            fbf1 = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf1[0] != "(":
                fbf1 = "(" + fbf1 + ")"
            fbf2 = "({})".format(self.args[1].str_wo_sign()) \
                if self.args[1].char \
                else self.args[1].str_wo_sign()
            if len(self.args[1].args) > 1 and fbf2[0] != "(":
                fbf2 = "(" + fbf2 + ")"
            txt += "{} {} {}".format(fbf1, self.char, fbf2)
        elif self.char:
            fbf = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf[0] != "(":
                fbf = "(" + fbf + ")"
            txt += "{}{}".format(self.char, fbf)
        else:
            txt += self.args
        return txt

    def str_wo_sign(self):
        if len(self.args) > 1 and self.char:
            fbf1 = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf1[0] != "(":
                fbf1 = "(" + fbf1 + ")"
            fbf2 = "({})".format(self.args[1].str_wo_sign()) \
                if self.args[1].char \
                else self.args[1].str_wo_sign()
            if len(self.args[1].args) > 1 and fbf2[0] != "(":
                fbf2 = "(" + fbf2 + ")"
            return "{} {} {}".format(fbf1, self.char, fbf2)
        elif self.char:
            fbf = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf[0] != "(":
                fbf = "(" + fbf + ")"
            return "{}{}".format(self.char, fbf)
        else:
            return self.args

    def get_param(self):
        "Get assigned parameteres of a formula"
        return get_all(map(lambda f: f.get_param(),
                           self.args))

    def get_all_param(self):
        "Get all parameters of a formula"
        return get_all(map(lambda f: f.get_all_param(),
                           self.args))

    def __eq__(self, other):
        # Two formulas are equal only when variables and function are the same
        return self.args == other.args and self.char == other.char

    def closed(self, other):
        "Check if the formula is closed by the argument"
        T = {"T", "Tc"}
        F = {"F", "Fc"}
        return self == other and \
            ((self.sign in T and other.sign in F) or
             (self.sign in F and other.sign in T))

    def __hash__(self):
        return hash(str(self))


class Atom(FBF):
    def __init__(self, value, sign=None):
        "The atomic element"
        self.args = value
        self.sign = sign
        self.char = ""

    def get_all_param(self):
        "Get all parameters"
        param = re.search(r"(?<=\()\w+(?=\))", self.args)
        return param.group() if param else []

    def get_param(self):
        "Return the parameter if assigned"
        param = re.search(r"(?<=\()p\d+(?=\))", self.args)
        if not param:
            return None
        return param.group() if len(param.group()) > 1 else None

    def set_param(self, val):
        "Set the parameter for first order rules"
        return Atom(re.sub(r"(?<=\()\w+(?=\))",
                           val,
                           self.args),
                    sign=self.sign)


class Et(FBF):
    def __init__(self, *args, sign=None):
        "The logical et connector"
        self.char = ET_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(Et(*args[0:2]), *args[2:])

    def set_param(self, param):
        "Set all parameters of a formula"
        return Et(self.args[0].set_param(param),
                  self.args[1].set_param(param),
                  sign=self.sign)

    def solve(self, solver, params):
        # just check a tableaux table
        fbf1, fbf2 = self.args
        if solver == "CL":
            fbf1.sign = self.sign
            fbf2.sign = self.sign
            if self.sign == "T":
                return [{fbf1, fbf2}], [False]
            elif self.sign == "F":
                return [{fbf1}, {fbf2}], [False, False]
        elif solver == "INT":
            fbf1.sign = self.sign
            fbf2.sign = self.sign
            if self.sign == "T":
                return [{fbf1, fbf2}], [False]
            elif self.sign in {"F", "Fc"}:
                return [{fbf1}, {fbf2}], [False, False]
        return [{self}], [False]


class Or(FBF):
    def __init__(self, *args, sign=None):
        "The logical Or connector"
        self.char = OR_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(Or(*args[0:2]), *args[2:])

    def set_param(self, param):
        "Set all parameters of a formula"
        return Or(self.args[0].set_param(param),
                  self.args[1].set_param(param),
                  sign=self.sign)

    def solve(self, solver, params):
        fbf1, fbf2 = self.args
        if solver == "CL":
            fbf1.sign = self.sign
            fbf2.sign = self.sign
            if self.sign == "T":
                return [{fbf1}, {fbf2}], [False, False]
            elif self.sign == "F":
                return [{fbf1, fbf2}], [False]
        elif solver == "INT":
            fbf1.sign = self.sign
            fbf2.sign = self.sign
            if self.sign == "T":
                return [{fbf1}, {fbf2}], [False, False]
            elif self.sign in {"F", "Fc"}:
                return [{fbf1, fbf2}], [False]
        return [{self}], [False]


class If(FBF):
    def __init__(self, *args, sign=None):
        "The logical if connector"
        self.char = IF_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(If(*args[0:2]), *args[2:])

    def set_param(self, param):
        "Set all parameters of a formula"
        return If(self.args[0].set_param(param),
                  self.args[1].set_param(param),
                  sign=self.sign)

    def solve(self, solver, params):
        fbf1, fbf2 = self.args
        if solver == "CL":
            if self.sign == "T":
                fbf1.sign = "F"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}], [False, False]
            else:
                fbf1.sign = "T"
                fbf2.sign = "F"
                return [{fbf1, fbf2}], [False]
        if solver == "INT":
            if self.sign == "T":
                if not fbf1.char:
                    fbf1.sign = "F"
                    fbf2.sign = "T"
                    return [{fbf1}, {fbf2}], [False, False]
                elif fbf1.char == ET_CHAR:
                    fbf = If(fbf1.args[0],
                             If(fbf1.args[1], fbf2),
                             sign="T")
                    return [{fbf}], [False]
                elif fbf1.char == OR_CHAR:
                    fbf1_new = If(fbf1.args[0], fbf2, sign="T")
                    fbf2_new = If(fbf1.args[1], fbf2, sign="T")
                    return [{fbf1_new, fbf2_new}], [False]
                elif fbf1.char == IF_CHAR:
                    fbf1_new = If(fbf1.args[0], fbf2, sign="T")
                    fbf2_new = If(fbf1.args[1], fbf2, sign="F")
                    fbf2.sign = "T"
                    return [{fbf1_new, fbf2_new}, {fbf2}], [False, False]
                elif fbf1.char == ALL_CHAR:
                    fbf1.char = "F"
                    fbf2.char = "T"
                    return [{fbf1, self}, {fbf2}], [False, False]
                elif fbf1.char == EXISTS_CHAR:
                    fbf_new = If(All(fbf1.args[0]), self.args[1], sign="T")
                    return [{fbf_new}], [False]
                else:
                    fbf1.sign = "F"
                    fbf2.sign = "T"
                    return [{self, fbf1}, {fbf2}], [False, False]
            elif self.sign == "F":
                fbf1.sign = "T"
                fbf2.sign = "F"
                return [{fbf1, fbf2}], [True]
            elif self.sign == "Fc":
                fbf1.sign = "T"
                fbf2.sign = "Fc"
                return [{fbf1, fbf2}], [True]
        return [{self}], [False]


class Not(FBF):
    def __init__(self, *args, sign=None):
        "The logical not operator"
        self.char = NOT_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) != 1:
            raise Exception("Object is not a valid formula")

    def set_param(self, param):
        "Set all parameters of a formula"
        return Not(self.args[0].set_param(param),
                   sign=self.sign)

    def solve(self, solver, params):
        fbf = self.args[0]
        if solver == "CL":
            fbf.sign = "F" if self.sign == "T" else "T"
            return [{fbf}], [False]
        elif solver == "INT":
            if self.sign == "T":
                fbf.sign = "Fc"
                return [{fbf}], [False]
            elif self.sign in {"F", "Fc"}:
                fbf.sign = "T"
                return [{fbf}], [True]
        return [{self}], [False]


class All(FBF):
    def __init__(self, *args, sign=None):
        "The logical quantifier all operator"
        self.char = ALL_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) != 1:
            raise Exception("Object is not a valid formula")

    def solve(self, solver, params):
        fbf = self.args[0]
        if not params:
            params = {"p1"}
        if solver == "CL":
            fbf.sign = self.sign
            if self.sign == "T":
                return [{fbf.set_param(p), self} for p in params], \
                    [False for p in params]
            elif self.sign == "F":
                return [{fbf.set_param(p_new(params))}], [False]
        elif solver == "INT":
            if self.sign == "T":
                fbf.sign = self.sign
                return [{fbf.set_param(p), self} for p in params], \
                    [False for p in params]
            elif self.sign == "F":
                fbf.sign = "F"
                return [{fbf.set_param(p_new(params))}], [True]
            elif self.sign == "Fc":
                fbf.sign = "F"
                return [{fbf.set_param(p_new(params)), self}], [True]
        return [{self}], [False]


class Exists(FBF):
    def __init__(self, *args, sign=None):
        "The logical existential all operator"
        self.char = EXISTS_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) != 1:
            raise Exception("Object is not a valid formula")

    def solve(self, solver, params):
        fbf = self.args[0]
        if not params:
            params = {"p1"}
        if solver == "CL":
            fbf.sign = self.sign
            if self.sign == "T":
                return [{fbf.set_param(p_new(params))}], [False]
            elif self.sign == "F":
                return [{fbf.set_param(p)} for p in params], \
                    [False for p in params]
        elif solver == "INT":
            fbf.sign = self.sign
            if self.sign == "T":
                return [{fbf.set_param(p_new(params))}], [False]
            elif self.sign == "F":
                return [{fbf.set_param(p)} for p in params], \
                    [False for p in params]
            elif self.sign == "Fc":
                return [{fbf.set_param(p), self} for p in params], \
                    [False for p in params]
        return [{self}], [False]


class Tableaux:
    def __init__(self, solver, S, old_S=list(), max_p=0, first_run=False):
        self.solver = solver
        if first_run:
            S[0].sign = "F"
        self.S = set(S)
        # to check if the recoursive algorithm enters in a loop
        self.old_S = old_S
        self.max_p = max_p if max_p else len(S[0].get_all_param())
        self.params = set(get_all(map(lambda f: f.get_param(),
                                      self.S)))
        if solver == "CL":
            certain = {"T", "F"}
        elif solver == "INT":
            certain = {"T", "Fc"}
        else:
            raise Exception("Not a valid logic")
        self.Sc = set(filter(lambda f: f.sign in certain,
                             self.S))

    def is_closed(self):
        for fbf in self.S:
            if any(map(lambda f: fbf.closed(f), self.S - {fbf})):
                return True
        return False

    def expand_solution(self, fbf):
        s, c = fbf.solve(self.solver, self.params)
        # if a sequence is correct, this is the solution
        return all([Tableaux(self.solver,
                             list(((self.Sc if c[i] else
                                    self.S) - {fbf}) | s[i]),
                             old_S=self.old_S + [self.S],
                             max_p=self.max_p).solve()
                    for i in range(len(s))])

    def solve(self):
        # check if the tableaux is closed
        if self.is_closed():
            return True
        # get all formulas which a rule can be applied to
        not_atomic = set(filter(lambda f: f.char, self.S))
        # if any, the tableaux is open
        if self.S in self.old_S or \
           not not_atomic or \
           (self.params and len(self.params) > self.max_p):
            return False
        # check if exists a sequence of formulas that closed the tableaux
        # with an exploratory algorithm: it checks all possible sequences
        return any(map(self.expand_solution, not_atomic))


def is_theorem(formula, logic):
    "Check if a formula is a theorem in a logic"
    try:
        return Tableaux(logic, [formula], first_run=True).solve()
    except RecursionError:
        print("Error, cannot say neither if it is valid nor " +
              "not valid in {} logic".format(logic))
        return None


def solve(formula, logic=["CL", "INT"]):
    "Solve the formula the result"
    txt = str(formula)
    results = {l: is_theorem(formula, l)
               for l in logic}
    print(txt)
    for l, r in results.items():
        print(l + " "*(5 - len(l)) + (THEOREM_CHAR if r
                                      else NOT_THEOREM_CHAR) + "  " + txt)
    print("")
    return results


if __name__ == "__main__":
    solve(If("A", "B", "A", "A", "B", "B"))
    solve(Or("A", Not("A")))
    solve(Not(Not(Or("A", Not("A")))))
    solve(Et("A", Not("A")))
    solve(Not(Et("A", Not("A"))))
    solve(If(Et(Or("P", "Q"),
                If("P", "R"),
                Et(Not("P"),
                   If("Q", "R"))),
             "R"))
    solve(If(Or("A", Not("A")),
             "B", Not(Not("B"))))
    solve(If("A", Not(Not("A"))))
    solve(If(Not(Not("A")), "A"))
    solve(If(Not(Not((Not("A")))), Not("A")))

    # first order
    # solve(If(All(Or("A(x)",
    #                 "B(x)")),
    #          Or(All("A(x)"),
    #             All("B(x)"))))
    solve(If(All("A(x)"),
             Not(Exists(Not("A(x)")))))
    solve(If(Not(Exists(Not("A(x)"))),
             All("A(x)")))
    solve(If(All(If("A", "B(x)")),
             If("A",
                All("B(x)"))))
    solve(If(If("A",
                All("B(x)")),
             All(If("A",
                    "B(x)"))))
    solve(If(Exists(If("A(x)",
                       "B(x)")),
             If(All("A(x)"),
                Exists("B(x)"))))
    solve(If(If(All("A(x)"),
                Exists("B(x)")),
             Exists(If("A(x)",
                       "B(x)"))))
    solve(All(Or("A(x)", Not("A(x)"))))
    solve(Not(Not(All(Or("A(x)",
                         Not("A(x)"))))))
    solve(Exists(Or("A(x)",
                    Not("A(x)"))))
    solve(Not(Not(Exists(Or("A(x)",
                            Not("A(x)"))))))
