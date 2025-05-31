"""
05/31/2025 --- Arman Vossoughi
Programming Assignment 1 - CS391x
Implementation of Interportor from lambda1.dats
"""

"""
datatype term =
| TMvar of strn
| TMlam of (strn, term)
| TMapp of (term, term)
"""

"""
Parent class for representing the different types in lambda calculus: var, abstraction, application
"""
class term:
    # ctag represents what type of term this class is
    # this is the root class
    ctag = ""

    #defaults to this as a fall back
    def __str__(self):
        return ("term(" + self.ctag + ")")

"""
Subclass for var term (names x, y, z...)
"""
class term_var(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMvar"

    def __str__(self):
        return ("TMvar(" + self.arg1 + ")")

"""
LamTerm subclass (lambda abstraction)
"""
class term_lam(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMlam"

    def __str__(self):
        # Left arg (arg1) is already a string because it is a bound variable
        return ("TMlam(" + self.arg1 + ", " + str(self.arg2) + ")")
    
"""
AppTerm subclass (function application)
"""
class term_app(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMapp"

    def __str__(self):
        # Left arg (arg1) is already a string because it is a bound variable
        return ("TMapp(" + str(self.arg1) + ", " + str(self.arg2) + ")")

"""
Subclass for int term for extended lam calc (1,2,3...)
"""
class term_int(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMint"
    def __str__(self):
        return f"TMint({self.arg1})"

"""
Subclass for boolean term, True or False
"""
class term_btf(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMbtf"
    def __str__(self):
        return f"TMbtf({self.arg1})"
    
"""
Subclass for if then else term
"""
class term_if0(term):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "TMif0"

    def __str__(self):
        return f"TMif0({str(self.arg1)}, {str(self.arg2)}, {str(self.arg3)})"
    
"""
Subclass for operator term, +, -, /, *, %, <=, <, ==, >, >=, ||, &&, etc
"""
class term_op(term):
    def __init__(self, arg1, arg2):
        if len(arg2) != 2:
            raise TypeError("Did not provide a tuple of size 2 for operator term")
        
        self.arg1 = arg1
        self.arg2 = arg2[0]
        self.arg3 = arg2[1]
        self.ctag = "TMop"

    def __str__(self):
        return f"TMop({self.arg1}, {self.arg2}, {self.arg3})"

def subst_term(tm0, x00, sub):
    """
    Function for implementing a naive subsitution

    Input: Takes syntax tree -- tm0, term to be subsituted -- x00, and substitution term -- sub
    """
    def subst(tm0):
        return subst_term(tm0, x00, sub)

    if (tm0.ctag == "TMint"):
        return tm0
    
    if (tm0.ctag == "TMbtf"):
        return tm0
    
    if (tm0.ctag == "TMop"):
        operator = tm0.arg1
        tm1 = tm0.arg2
        tm2 = tm0.arg3
        return term_op(operator, (subst(tm1), subst(tm2)))
    
    if (tm0.ctag == "TMif0"):
        return term_if0(subst(tm0.arg1), subst(tm0.arg2), subst(tm0.arg3))
    
    if (tm0.ctag == "TMvar"):
        x01 = tm0.arg1
        return sub if (x00==x01) else tm0
    
    if (tm0.ctag == "TMlam"):
        x01 = tm0.arg1
        tm1 = tm0.arg2
        return tm0 if (x00==x01) else term_lam(x01, subst(tm1))
    
    if (tm0.ctag == "TMapp"):
        tm1 = tm0.arg1
        tm2 = tm0.arg2
        return term_app(subst(tm1), subst(tm2))
    
    #if we get here something went wrong, need to raise type error
    raise TypeError(tm0) 

BASICTYPES = ["TMint", "TMbtf", "TMvar", "TMlam"]
def term_interp(tm0: term) -> term:
    """
    Function for handling evaluation of our lambda expressions.

    Input: Takes a term and outputs the result as a term
    """ 
    
    #for the following 4 we just return the term as is 
    # case+ tm0 of
    #     | TMint _ => tm0
    #     | TMbtf _ => tm0
    #     | TMvar _ => tm0

    #     (* when we see a lambda term, we treat is as a value: forbidden door---don't go in *)
    #     | TMlam _ => tm0

    #basic types defined above
    if tm0.ctag in BASICTYPES:
        return tm0
    
    #   | TMapp (tm1, tm2) => let val tm1 = term_interp(tm1) in 
    #     (
    #         case+ tm1 of
    #         | TMlam(x01, tmx) => term_interp(term_subst(tmx, x01, tm2))
    #         | _ (*None Lambda Form*) => TMapp(tm1, term_interp(tm2))
    #     )

    if tm0.ctag == "TMapp":
        tm1 = term_interp(tm0.arg1)
        tm2 = tm0.arg2

        #beta reduction case (first term is lambda expression)
        if tm1.ctag == "TMlam":
            return term_interp(subst_term(tm1.arg2, tm1.arg1, tm2))
        else:
            return term_app(tm1, term_interp(tm2))

    if tm0.ctag == "TMop":
        #turns out python did introduce a pattern match in ver 3.10!
        #I also added some basic type checking
        match tm0.arg1:
            case "+":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_int(val1 + val2)
            case "-":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_int(val1 - val2)
            
            # division has a special case for div by zero
            case "/":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                if val2 == 0:
                    raise ZeroDivisionError("Second Value is 0, Division by Zero Error")
                return term_int(val1 + val2)
            
            case "*":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_int(val1 * val2)
            case "%":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_int(val1 % val2)
            
            # both arguments must be of the same type for comparison
            # some languages support 0 or 1 as boolean encodings but I'm assuming we stick stricly to T/F
            case "==":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                if type(val1) == int and type(val2) == int:
                    return term_btf(val1 == val2)
                if type(val1) == bool and type(val2) == bool:
                    return term_btf(val1 == val2)
                raise(TypeError(f"first argument type: {str(val1)}  != second argument type: {str(val2)}"))
            
            case "!=":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1

                if type(val1) == int and type(val2) == int:
                    return term_btf(val1 != val2)
                if type(val1) == bool and type(val2) == bool:
                    return term_btf(val1 != val2)
                
                raise(TypeError(f"first argument type: {str(val1)}  != second argument type: {str(val2)}"))
            
            case "<=":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 <= val2)
            
            case "<":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 < val2)
            
            case ">":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 > val2)
            
            case ">=":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 >= val2)
            
            case "||":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 or val2)
            
            case "&&":
                val1 = term_interp(tm0.arg2).arg1
                val2 = term_interp(tm0.arg3).arg1
                return term_btf(val1 and val2)
        
            case _:
                raise TypeError(f"Invalid operator {str(tm0)}")
            
    if tm0.ctag == "TMif0":
        condition = term_interp(tm0.arg1).arg1
        tCase = tm0.arg2
        fCase = tm0.arg3
        return term_interp(tCase) if condition else term_interp(fCase)

# helper functions to make lambda syntax easier to write
# fun TMlte(Ttm1: term, tm2) = TMopr("<=", list@(tm1,tm2))
# fun TMgte(Ttm1: term, tm2) = TMopr(">=", list@(tm1,tm2))
# fun TMlt(Ttm1: term, tm2) = TMopr("<", list@(tm1,tm2))
# fun TMgt(Ttm1: term, tm2) = TMopr(">", list@(tm1,tm2))
# fun TMneq(Ttm1: term, tm2) = TMopr("!=", list@(tm1,tm2))
# fun TMmul(Ttm1: term, tm2) = TMopr("*", list@(tm1,tm2))
# fun TMdiv(Ttm1: term, tm2) = TMopr("/", list@(tm1,tm2))
# fun TMmod(Ttm1: term, tm2) = TMopr("%", list@(tm1,tm2))
# fun TMadd(Ttm1: term, tm2) = TMopr("+", list@(tm1,tm2))
# fun TMsub(Ttm1: term, tm2) = TMopr("-", list@(tm1,tm2))

def TMlte(tm1: term, tm2):
    return term_op("<=", [tm1, tm2])  

def TMgte(tm1: term, tm2):
    return term_op(">=", [tm1, tm2])   

def TMlt(tm1: term, tm2):
    return term_op("<", [tm1, tm2])   

def TMgt(tm1: term, tm2):
    return term_op(">", [tm1, tm2])   

def TMeq(tm1: term, tm2):
    return term_op("==", [tm1, tm2])   

def TMneq(tm1: term, tm2):
    return term_op("!=", [tm1, tm2])   

def TMadd(tm1: term, tm2):
    return term_op("+", [tm1, tm2])   

def TMsub(tm1: term, tm2):
    return term_op("-", [tm1, tm2])     

def TMmul(tm1: term, tm2):
    return term_op("*", [tm1, tm2])    

def TMdiv(tm1: term, tm2):
    return term_op("/", [tm1, tm2])    

def TMmod(tm1: term, tm2):
    return term_op("%", [tm1, tm2])    

def testSuite():
    #fixed point operator to enable recursion
    Y = term_lam("f", term_app(term_lam("x", term_app(term_var("f"), term_app(term_var("x"), term_var("x")))), term_lam("x", term_app(term_var("f"), term_app(term_var("x"), term_var("x"))))))

    # val TMfact = Y(F) where{
    # val f = TMVar"f"
    # val x = TMvar"x"
    # val F = TMlam("f", TMlam("x", TMif0(TMlte(x, TMint(0)), TMint(1), TMmul(x, TMapp(f, TMsub(x, TMint(1)))))))

    fact = term_lam("f", term_lam("x", term_if0(TMlte(term_var("x"), term_int(0)), term_int(1), TMmul(term_var("x"), term_app(term_var("f"), TMsub(term_var("x"), term_int(1)))))))

    fact = term_app(term_app(Y, fact), term_int(5))
    print(term_interp(fact))

def main():
    print("Main invoked")
    testSuite()

if __name__ == "__main__":
    main()