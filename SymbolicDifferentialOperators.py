# -*- coding: utf-8 -*-
"""
Created on Mon Mar  1 17:43:15 2021

Fichiers contenant des fonctions pour faire du calcul
formel en relativité
@author: Pascal
"""

from sympy import *
from sympy.diffgeom import *
from IPython.display import display, Math, Latex, Image
from IPython.lib.latextools import latex_to_png, latex_to_png_dvipng
#from sympy.printing.latex import LatexPrinter, print_latex
from sympy.physics.quantum.dagger import Dagger
from sympy.core.exprtools import Factors

init_printing(use_latex = True)


def collectWithFactorizedCoeff(f, collectVariable):
    """Function used by lightSimp. It collect the terms of f with respect to collectVariable but keep the monomial in a factorized form"""
    dictTerm = f.expand().collect(collectVariable, evaluate = False)
    res = Integer(0)
    for key in dictTerm:
        res  = Add(res, Mul(key,factor_terms(dictTerm[key])))
    return res
   
def lightSimp(expr, collect = None):
    """Basic simplification function, faster than the simplify function of sympy, the second argument enable to collect the terms with respect to a particular variable"""
    variables, reducedExpr = cse(expr)
    reducedExpr = reducedExpr[0].expand().powsimp()
    variables.reverse()
    for newv, oldv in variables:
        reducedExpr = reducedExpr.subs(newv,oldv)
    reducedExpr = reducedExpr.powsimp()
    f,g = reducedExpr.as_numer_denom()
    f = factor_terms(f)
    g = factor_terms(g)
    F = Factors(f)
    G = Factors(g)
    F,G = F.normal(G)
    f = F.as_expr()
    g = G.as_expr()
    expandedf = f.expand()
    if count_ops(expandedf)< count_ops(f):
        f = expandedf 
    try:
        Q, r = reduced(f, [g], field=True, expand=False)
    except ComputationFailed:
        return f/g
    if collect:
        return collectWithFactorizedCoeff(Add(*Q),collect) + (collectWithFactorizedCoeff(r,collect)/g)
    else:
        return Add(*Q)+(r/g)
    

class DOperator:
    """class to represent differential operators"""
    def __init__(self, coeff, variables = [], orders = [], order = "prefix"):
        if variables == []:
            variables_copy = [1]
            orders_copy = [[0]]
        elif orders == [] and len(variables)==1:
            variables_copy = variables.copy()
            orders_copy = [[1]]
        else:
            orders_copy = orders.copy()
            variables_copy = variables.copy()
        
        if not len(coeff)==len(orders_copy):
            print("coeffs:")
            print(coeff)
            print("orders:")
            print(orders_copy)
            raise Exception("Le nombre d'ordres:"+str(len(orders_copy))+" ne correspond pas au nombre de coefficients:" + str(len(coeff)))
            return None
        coeff_copy = []
        for i in range(0,len(coeff)):
            if isinstance(coeff[i], Expr):
                coeff_copy.append(coeff[i])
            elif isinstance(coeff[i], int):
                coeff_copy.append(Integer(coeff[i]))
            else:
                raise Exception("L'un des coefficients n'est pas une expression sympy ni un entier")
        self.coeff = coeff_copy
        self.orders = orders_copy
        self.variables = variables_copy
        self.order = order
        
    def __str__(self):
        res = ""
        for i in range(0, len(self.coeff)):
            expr=self.coeff[i]
            orders = self.orders[i]
            if expr == Integer(1) and sum(orders)>0:
                term = ""
            elif expr ==Integer(-1) and sum(orders)>0:
                term = " - "
            else:
                term = latex(expr)
            if expr.func == Add:
                term = "\\left(" + term + "\\right)"
            for j in range(0,len(orders)):
                if orders[j] == 1:
                    term += "\\partial_{"+latex(self.variables[j])+"} "
                if orders[j] > 1:
                    term += "\\partial_{"+latex(self.variables[j])+"}"+"^"+str(orders[j])
            if res=="":
                res += term
            elif expr.func == Mul and isinstance(expr.args[0], Integer) and expr.args[0]<0:
                res += term
            elif isinstance(expr, Integer) and expr<0:
                res += term
            else:
                res = res + "+" + term
        if res=="":
            res = '0'
        return res
    
    def __add__(self,d):
        if(isinstance(d, Expr)):
            p = DOperator([d])
        elif(isinstance(d, int)):
            p = DOperator([Integer(d)])
        elif(isinstance(d, DOperator)):
            p = d.copy()
        else:
            raise Exception("Unsupported operation between DOperator and "+str(type(d)))
        q = self.copy()
        new_variables = []
        new_variables_index = []
        for i in range(0,len(p.variables)):
            if not p.variables[i] in self.variables:
                new_variables.append(p.variables[i])
                new_variables_index.append(i)
        res_variables = self.variables + new_variables
        p.changeVariableOrder(res_variables)
        q.changeVariableOrder(res_variables)
        res_coeff = q.coeff
        res_orders_list = q.orders
        for j in range(0,len(p.coeff)):
            try:
                k = res_orders_list.index(p.orders[j])
                res_coeff[k] += p.coeff[j]
                #res_coeff[k] = res_coeff[k].simplify()
            except ValueError:
                res_coeff.append(p.coeff[j])
                res_orders_list.append(p.orders[j])
        res = DOperator(res_coeff,  res_variables, res_orders_list)
        #res.simplifyCoeff()
        return res
    def __radd__(self, d):
        if(isinstance(d, Expr)):
            p = DOperator([d])
        elif(isinstance(d, int)):
            p = DOperator([Integer(d)])
        elif(isinstance(d, DOperator)):
            p = d.copy()
        else:
            raise Exception("Unsupported operation between DOperator and "+str(type(d)))
        return p+self
    
    def __mul__(self, fact2):
        if type(fact2) == int:
            fact2_copy = DOperator([Integer(fact2)])
        elif isinstance(fact2, Expr):
            fact2_copy = DOperator([fact2])
        elif isinstance(fact2, DOperator):
            fact2_copy = fact2.copy()
        else:
            print("Le facteur problématique est: ")
            print(fact2)
            raise Exception("L'un des facteurs n'est pas convertible en DOperator")
        fact1 = self.copy()
        DOperator.sameVariables(fact1, fact2_copy)
        res = DOperator([Integer(0)])
        for i in range(0, len(self.coeff)):
            for j in range(0, len(fact2_copy.coeff)):
                res = res + DOperator.mulMonome(DOperator([fact1.coeff[i]],fact1.variables,[fact1.orders[i]]),DOperator([fact2_copy.coeff[j]],fact2_copy.variables, [fact2_copy.orders[j]]))
        return res
            
    def __rmul__(self, fact2):
        if type(fact2) == int:
            fact2_copy = DOperator([Integer(fact2)])
        elif isinstance(fact2, Expr):
            fact2_copy = DOperator([fact2])
        elif isinstance(fact2, DOperator):
            fact2_copy = fact2.copy()
        else:
            print("L'un des facteurs n'est pas convertible en DOperator")
        
        return fact2_copy*self
    
    def __neg__(self):
        return (-1)*self
    
    def __sub__(self, fact2):
        return self + (-fact2)
    def __rsub__(self, fact1):
        return fact1+(-self)
    
    def _ipython_display_(self):
        display(Image(data = latex_to_png_dvipng(self.__str__(),wrap = True)))
        
    
    def copy(self):
        return DOperator(self.coeff, self.variables, self.orders, self.order)
    
    def replace(self, operator):
        # copy the content of operator into self
        self.coeff = operator.coeff
        self.orders = operator.orders
        self.variables = operator.variables
        self.order = operator.order
        
    def changeVariableOrder(self, new_variables):
        new_places = [0]*len(self.variables)
        for j in range(0, len(self.variables)):
            try:
                new_places[j]=new_variables.index(self.variables[j])
            except ValueError:
                "Le nouvel ordre de variable ne contient pas l'une des variables d'origine"
        new_coeff = []
        new_orders_list = []
        for k in range(0, len(self.coeff)):
            expr = self.coeff[k]
            orders = self.orders[k]
            new_orders = [0]*len(new_variables)
            for j in range(0,len(orders)):
                new_orders[new_places[j]] = orders[j]
            new_coeff.append(expr)
            new_orders_list.append(new_orders)
        self.variables = new_variables
        self.coeff = new_coeff
        self.orders = new_orders_list
        
    
    def simplifyCoeff(self):
        zeroIndex = []
        for j in range(0, len(self.coeff)):
            self.coeff[j] = self.coeff[j].simplify()
            if self.coeff[j] == Integer(0):
                zeroIndex.append(j)
        self.coeff = [self.coeff[i] for i in range(0, len(self.coeff)) if not i in zeroIndex]
        self.orders = [self.orders[i] for i in range(0, len(self.orders)) if not i in zeroIndex]
    def lightSimpCoeff(self, collectVariable = None):
        zeroIndex = []
        for j in range(0, len(self.coeff)):
            self.coeff[j] = lightSimp(self.coeff[j], collectVariable)
            if self.coeff[j] == Integer(0):
                zeroIndex.append(j)
        self.coeff = [self.coeff[i] for i in range(0, len(self.coeff)) if not i in zeroIndex]
        self.orders = [self.orders[i] for i in range(0, len(self.orders)) if not i in zeroIndex]
    def customSimp(self, simpFunc):
        zeroIndex = []
        for j in range(0, len(self.coeff)):
            self.coeff[j] = customFunc(self.coeff[j])
            if self.coeff[j] == Integer(0):
                zeroIndex.append(j)
        self.coeff = [self.coeff[i] for i in range(0, len(self.coeff)) if not i in zeroIndex]
        self.orders = [self.orders[i] for i in range(0, len(self.orders)) if not i in zeroIndex]
    def mulMonome(f1, f2):
        """Les monomes doivent avoir les mêmes variables dans le même ordre"""
        if not f1.variables == f2.variables:
            print("Variables du premier facteur: ")
            print(f1.variables)
            print("Variables du second facteur: ")
            print(f2.variables)
            raise Exception("Les monômes doivent avoir les mêmes ensembles de variables")
        if f1.totalOrder() == 0:
            return DOperator([f1.coeff[0]*f2.coeff[0]], f2.variables, [f2.orders[0]])
        else:
            orders1 = f1.orders[0].copy()
            orders2 = f2.orders[0].copy()
            for i in range(0, len(orders1)):
                if orders1[i]>0:
                    orders1[i] -=1
                    orders2[i] +=1
                    return DOperator.mulMonome(DOperator(f1.coeff, f1.variables, [orders1]), DOperator(f2.coeff, f2.variables, [orders2]))+DOperator.mulMonome(DOperator(f1.coeff, f1.variables, [orders1]), DOperator([f2.coeff[0].diff(f1.variables[i])], f2.variables, f2.orders))
    def totalOrder(self):
        maxi = 0
        for i in range(0, len(self.orders)):
            ordTerm = sum(self.orders[i])
            if ordTerm>maxi:
                maxi = ordTerm
        return maxi
    def sameVariables(op1, op2):
        """Fait dépendre les opérateurs passés en argument des mêmes variables (dans le même ordre). Attention, modifie les arguments!"""
        new_variables = []
        for i in range(0,len(op2.variables)):
            if not op2.variables[i] in op1.variables:
                new_variables.append(op2.variables[i])
        res_variables = op1.variables + new_variables
        op1.changeVariableOrder(res_variables)
        op2.changeVariableOrder(res_variables)
        
    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent<0:
            raise Exception("The exponent should be a non negative integer")
        elif exponent == 0:
            return DOperator([Integer(1)])
        else:
            binary = "{0:b}".format(exponent)
            operatorPower = [None]*len(binary)
            operatorPower[0] = self.copy()
            for i in range(1,len(binary)):
                operatorPower[i] = operatorPower[i-1]*operatorPower[i-1]
            res = DOperator([Integer(1)])
            binaryReverse = binary[::-1]
            for i in range(0, len(binary)):
                if(binaryReverse[i]=='1'):
                    res = operatorPower[i]*res
            return res
    
    def adj(self, volumeForm = Integer(1)):
        if not isinstance(volumeForm, Expr):
            raise Exception("The argument of ^ should be a volume form (therefore a sympy expression)")
        res = DOperator([0])
        for i in range(0, len(self.coeff)):
            res = res + (-1)**(sum(self.orders[i]))* 1/volumeForm*DOperator([1],self.variables, [self.orders[i]])*conjugate(self.coeff[i])*volumeForm
        return res
    
    def substituteInCoeff(self, expr1, expr2):
        for i in range(0,len(self.coeff)):
            self.coeff[i] = self.coeff[i].subs(expr1, expr2)
    def substituteInDerivative(self, oldDerivative, newOperator):
        #Replace a derivative with a new differential operator
        res = DOperator([0])
        for i in range(0,len(self.coeff)):
            monome = DOperator([1])
            for j in range(0, len(self.orders[i])):
                if self.variables[j]==oldDerivative:
                    monome = monome*(newOperator)**(self.orders[i][j])
                else:
                    monome = monome*(DOperator([1],[self.variables[j]]))**(self.orders[i][j])
            res = res + self.coeff[i]*monome
        self.replace(res.copy())
        return res
        
    def apply(self, expr):
        res = Integer(0)
        for i in range(0, len(self.coeff)):
            term = expr
            for j in range(0, len(self.variables)):
                if self.orders[i][j]>0:
                    term = term.diff(self.variables[j], self.orders[i][j])
            res = res + self.coeff[i]*term
        return res
    def changeOneVariable(self, oldVariable, valueWRTnew, newVariable):
        #Make a change of 1 variable, the valueWRTnew must not depend on other variable than the new one
        self.substituteInCoeff(oldVariable, valueWRTnew)
        derivative = valueWRTnew.diff(newVariable)
        Dold = DOperator([derivative**(-1)], [newVariable])
        self.substituteInDerivative(oldVariable, Dold)
    def substituteOnePartialDerivative(self, variableOfTheOpToReplace, newOperator):
        res = DOperator([0])
        for i in range(0, len(self.coeff)):
            term = DOperator([self.coeff[i]])
            for j in range(0, len(self.variables)):
                if self.variables[j] != variableOfTheOpToReplace:
                    term = term*(DOperator([1], [self.variables[j]]))**self.orders[i][j]
                else:
                    term = term*(newOperator)**self.orders[i][j]
            res = res+ term
        return res
    def getCoeff(self, variableName=[], variableOrders=[]):
        #Get the coefficient indicated by the two arguments for example [r,theta], [2,1] return the coeff of partial_r^2partial_theta. Warning, only indicate variables with positive orders
        res = Integer(0)
        for j in range(0,len(variableName)):
                if variableName[j] not in self.variables:
                    return Integer(0)
                
        for i in range(0,len(self.coeff)):
            currentOrders = self.orders[i]
            isEqual = True
            for j in range(0,len(self.variables)):
                try:
                    pos = variableName.index(self.variables[j])
                    if variableOrders[pos]!= currentOrders[j]:
                        isEqual = False
                        break
                except ValueError:
                    if currentOrders[j]!=0:
                        isEqual = False
                        break
            if isEqual:
                res += self.coeff[i]
        return res
    def getPrincipalOrder(self):
        #return the principal part of the operator (with convention coefficients on the left, derivative on the right)
        res = self.copy()
        totalOrder = res.totalOrder()
        for i in range(0, len(res.coeff)):
            if sum(res.orders[i])!=totalOrder:
                res.coeff[i]=Integer(0)
        return res
    def changeVariables(self, oldVariables, newVariables, oldWRTNew, newWRTOld):
        #Make a general change of variables (in place). Note that you have to give the relation in both directions
        #We create intermediary variables so that the oldVariables can have the same names that new ones
        if len(oldVariables)!= len(newVariables):
            raise("Not the same number of new and old variables")
        if len(oldWRTNew)!=len(newWRTOld) or len(newWRTOld)!=len(oldVariables):
            raise("Not the good number of relations between variables")
        transition = []
        n = len(oldVariables)
        for i in range(0,n):
            transition.append(symbols("x_"+str(i)))
            
        oldWRTTransition = oldWRTNew[:]
        for i in range(0,n):
            for j in range(0,n):
                oldWRTTransition[i] = oldWRTTransition[i].subs(newVariables[j], transition[j])
        
        for i in range(0, n):
            oldDerivativeWRTNew = DOperator([0])
            for j in range(0,n):
                coeff = newWRTOld[j].diff(oldVariables[i])
                for k in range(0,n):
                    coeff = coeff.subs(oldVariables[k], oldWRTTransition[k])
                oldDerivativeWRTNew = oldDerivativeWRTNew+coeff*DOperator([1],[transition[j]])
            self.substituteInDerivative(oldVariables[i],oldDerivativeWRTNew)
                
        for i in range(0,n):
            self.substituteInCoeff(oldVariables[i], oldWRTTransition[i])
        for i in range(0,n):
            self.substituteInDerivative(transition[i], DOperator([1],[newVariables[i]]))
            self.substituteInCoeff(transition[i], newVariables[i])
       
        
