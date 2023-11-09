import nltk
from z3 import *
def extract_variables(fol_str):
    variables = []
    for idx, char in enumerate(fol_str):
        if char in ['∀', '∃']:
            # Assumes the next character is the variable.
            # Make sure there are no spaces between quantifiers and variables.
            variables.append(fol_str[idx + 1])
    return variables
def formula(node,constants=None):
    if isinstance(node, str):  # Terminal node
        return node

    label = node.label()
    children = [formula(child) for child in node]

    if label == 'S':
        quant_part = children[0]
        body_part = children[1]
        # No need to close parenthesis here; it will be closed after the body part.
        return f'{quant_part} {body_part}'

    elif label == 'Q':
            # Extract quantifier and variable
            quant = children[0]
            var = children[1]
            # Start the quantifier string
            quant_str = f'({quant} (({var} Int))'

            # Check if there's a nested 'Q' node
            if len(node) == 3:
                # Continue with the nested quantifiers without closing the current one
                nested_quant = formula(children[2])
                quant_str += f' {nested_quant}'
            else:
                # If there's no nested 'Q', we do not close the parenthesis here
                # It will be closed at the end of the assert statement
                quant_str += ' '

            return quant_str


    elif label == 'F':
        # Check for nested 'F' formulas and handle parentheses
        if len(children) == 3 and children[0] == '(' and children[2] == ')':
            # If the 'F' node is surrounded by parentheses, process the middle child.
            return formula(children[1])
        elif len(children) == 1:
            # Single child, could be a negation, an atomic formula, or a nested 'F'
            return formula(children[0])
        else:
            # Find 'OP' nodes and construct the binary operation, ignoring parentheses
            op_nodes = [child for child in node if isinstance(child, nltk.tree.Tree) and child.label() == 'OP']
            if op_nodes:
                # Assuming there's only one operator in the binary operation
                op_node = op_nodes[0]
                op_index = node.index(op_node)
                # Handle operands, skip the parentheses
                left = formula(node[op_index - 1])
                op = formula(op_node)  # Process the operator node
                right = formula(node[op_index + 1])
                return f'({op} {left} {right})'
            else:
                # Handle cases where 'F' is not a negation or binary operation
                return ' '.join([formula(child) for child in node if child not in ('(', ')')])

    elif label == 'OP':
        op_map = {'→': '=>', '∧': 'and', '∨': 'or', '↔': '=', '⊕': 'xor'}
        # Since OP will be a tree with a single string child, we get the operator from its first child
        smtlib_op = op_map.get(node[0], node[0])
        return smtlib_op

    elif label == 'QUANT':
        # Translate the quantifier to the SMT-LIB equivalent
        quantifier_map = {'∀': 'forall', '∃': 'exists'}
        smtlib_quant = quantifier_map.get(children[0], children[0])
        return smtlib_quant
    elif label == 'L':
        # Literal, could be a predicate or a negated predicate
        if children[0] == '¬':
            # Negated predicate, expects ['¬', 'PRED', '(', 'TERMS', ')']
            pred = children[1]
            terms = children[3]
            return f'(not ({pred} {terms}))'
        else:
            # Predicate, expects ['PRED', '(', 'TERMS', ')']
            pred = children[0]
            terms = children[2]
            return f'({pred} {terms})'

    elif label == 'PRED':
        # Predicate name, just return the name
        return children[0]

    elif label == 'TERMS':
        # Multiple terms, separated by commas
        # Remove commas and return space-separated terms
        terms = [child for child in children if child != ',']
        return ' '.join(terms)

    elif label == 'TERM':
        # A single term, could be a constant or a variable
        return children[0]

    elif label == 'CONST' or label == 'VAR':
        # Constant or variable, just return the name
        return children[0]

    # Add more cases as needed for other node types
    else:
        raise ValueError(f'Unknown node type: {label}')

def extract_predicates(node, variables):
    predicates = {}
    constants = set([])
    def traverse(node):
        if isinstance(node, str):
            return

        label = node.label()
        children = [child for child in node]
        if label == 'CONST':
            if not (node[0] in variables):
                constants.add(node[0])
        if label == 'L':
            if len(node)==4:
                # Extract predicate name
                pred_name = children[0][0]

                # Count arity based on the number of terms
                terms_node = children[2]  # This is the 'TERMS' node
                arity = (len(terms_node)+1)/2 #term1,term2,term3,... if it has len n then the terms are (n+1)/2

            elif len(node)==5:
                pred_name = children[1][0]

                # Count arity based on the number of terms
                terms_node = children[3]  # This is the 'TERMS' node
                arity = (len(terms_node)+1)/2
            # Add to predicates dictionary
            arity=int(arity)
            predicates[pred_name] = arity
        for child in children:
            traverse(child)

    traverse(node)
    return [predicates, constants]

def generate_smtlib_declarations(predicates, constants):
    declarations = []
    for pred_name, arity in predicates.items():
        # Generate the type signature (Int ...) based on arity
        type_signature = ' '.join(['Int' for _ in range(arity)])
        declarations.append(f"(declare-fun {pred_name} ({type_signature}) Bool)")
    for c in constants:
        # Generate the type signature (Int ...) based on arity
        type_signature = 'Int'
        declarations.append(f"(declare-const {c} {type_signature} )")
    return '\n'.join(declarations)

def fol_tree_to_smtlib(tree, variables):
  if len(tree)>1:
    quant_part = tree[0]
    body_part = tree[1]
    # This will hold the quantifier part of the SMT-LIB string
    quantifier_str = formula(quant_part)

    # This will hold the body part of the SMT-LIB string
    body_str = formula(body_part)

    # Now construct the final SMT-LIB string
    smtlib_str = f'(assert {quantifier_str} {body_str}'

        # Count the number of opened parentheses in the quantifier string to know how many to close
    num_open_parens = quantifier_str.count('(')
    num_close_parens = quantifier_str.count(')')
    difference = num_open_parens-num_close_parens
    # Close all parentheses at the end of the assert statement
    smtlib_str += ')' * (difference+1)
  else:
    body_part = tree[0]
    # This will hold the body part of the SMT-LIB string
    body_str = formula(body_part)
    smtlib_str = f'(assert {body_str})'


  # Now smtlib_str holds the entire SMT-LIB formula string
  predicates, constants = extract_predicates(tree, variables)
  declarations = generate_smtlib_declarations(predicates, constants)

  return declarations+'\n'+smtlib_str
