"""
Boolean Expression Simplifier
Minor Project - Digital Logic / Boolean Algebra
Student: NIRAJ VERMA | Scholar No: 319

Uses SymPy + custom Quine-McCluskey implementation
with step-by-step output and Karnaugh map support.
"""

from flask import Flask, render_template, request, jsonify
from sympy import symbols, simplify_logic, to_dnf, to_cnf
from sympy.logic.boolalg import And, Or, Not, Xor, Nand, Nor, Implies, Equivalent
from sympy.parsing.sympy_parser import (
    parse_expr, standard_transformations, implicit_multiplication_application
)
import traceback
import re
from itertools import product, combinations
from collections import defaultdict

app = Flask(__name__)

# -------------------------------------------------
#  Helper: clean / parse expression
# -------------------------------------------------

def preprocess_expression(expr):
    expr = expr.strip()
    # A' or A\'  ->  ~A   (common textbook notation for NOT)
    expr = re.sub(r"([A-Za-z_][A-Za-z0-9_]*)'", r"~\1", expr)
    reps = [
        (r'\bAND\b', '&'), (r'\band\b', '&'),
        (r'\bOR\b', '|'),  (r'\bor\b', '|'),
        (r'\bNOT\b', '~'), (r'\bnot\b', '~'),
        (r'\bXOR\b', '^'), (r'\bxor\b', '^'),
        (r'\bNAND\b', 'Nand'), (r'\bnand\b', 'Nand'),
        (r'\bNOR\b', 'Nor'),   (r'\bnor\b', 'Nor'),
        (r'→', '>>'), (r'->', '>>'), (r'⇒', '>>'),
        (r'↔', 'Equivalent'), (r'<->', 'Equivalent'), (r'⇔', 'Equivalent'),
        (r'!', '~'), (r'¬', '~'), (r'∧', '&'), (r'∨', '|'), (r'⊕', '^'),
        (r'\+', '|'),   # some books use + for OR
        (r'\.', '&'),   # some books use . for AND
    ]
    for pat, rep in reps:
        expr = re.sub(pat, rep, expr, flags=re.IGNORECASE)
    return expr


def extract_variables(expr_str):
    tokens = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expr_str)
    reserved = {
        'and', 'or', 'not', 'xor', 'nand', 'nor', 'true', 'false',
        'And', 'Or', 'Not', 'Xor', 'Nand', 'Nor', 'Implies', 'Equivalent',
        'True', 'False'
    }
    return sorted(set(t for t in tokens if t not in reserved))


def parse_boolean_expression(expr_str):
    cleaned = preprocess_expression(expr_str)
    var_names = extract_variables(cleaned)

    if not var_names:
        try:
            return parse_expr(cleaned, evaluate=False), []
        except Exception:
            raise ValueError("No variables found and expression is not constant.")

    syms = symbols(' '.join(var_names))
    if len(var_names) == 1:
        syms = (syms,)

    local_dict = {n: s for n, s in zip(var_names, syms)}
    local_dict.update({
        'And': And, 'Or': Or, 'Not': Not, 'Xor': Xor,
        'Nand': Nand, 'Nor': Nor, 'Implies': Implies, 'Equivalent': Equivalent,
        'True': True, 'False': False,
    })

    transformations = standard_transformations + (implicit_multiplication_application,)
    try:
        expr = parse_expr(
            cleaned, local_dict=local_dict,
            transformations=transformations, evaluate=False
        )
        return expr, var_names
    except Exception as e:
        raise ValueError(f"Parse error: {str(e)}")


# -------------------------------------------------
#  Truth table helpers
# -------------------------------------------------

def get_minterms(expr, var_names):
    """Return list of minterm indices where expression is True."""
    if not var_names:
        return [], []
    syms = symbols(' '.join(var_names))
    if len(var_names) == 1:
        syms = (syms,)
    n = len(var_names)
    minterms = []
    for i, vals in enumerate(product([0, 1], repeat=n)):
        subs = dict(zip(syms, vals))
        if bool(expr.subs(subs)):
            minterms.append(i)
    return minterms, list(range(n))


def generate_truth_table(expr, var_names, max_vars=6):
    if len(var_names) > max_vars:
        return None, f"Truth table limited to {max_vars} variables (got {len(var_names)})"
    if not var_names:
        return None, "No variables"
    syms = symbols(' '.join(var_names))
    if len(var_names) == 1:
        syms = (syms,)
    header = var_names + ['F']
    rows = []
    for vals in product([0, 1], repeat=len(var_names)):
        subs = dict(zip(syms, vals))
        result = int(bool(expr.subs(subs)))
        rows.append(list(vals) + [result])
    return {'header': header, 'rows': rows}, None


# -------------------------------------------------
#  Quine-McCluskey Algorithm (with steps)
# -------------------------------------------------

def binary_repr(num, bits):
    return format(num, f'0{bits}b')


def count_ones(s):
    return s.count('1')


def can_combine(a, b):
    """Return combined string with '-' if they differ by exactly one bit, else None."""
    diff = 0
    result = []
    for x, y in zip(a, b):
        if x != y:
            diff += 1
            result.append('-')
        else:
            result.append(x)
    if diff == 1:
        return ''.join(result)
    return None


def term_to_expression(term, var_names):
    """Convert a binary term (with -) to a product expression string."""
    parts = []
    for i, bit in enumerate(term):
        if bit == '1':
            parts.append(var_names[i])
        elif bit == '0':
            parts.append('~' + var_names[i])
    if not parts:
        return '1'
    return ' & '.join(parts)


def quine_mccluskey(minterms, num_vars, var_names):
    """
    Full Quine-McCluskey with detailed steps for the report.
    Returns (simplified_expr_string, steps_dict)
    """
    steps = {
        'minterms': [],
        'grouping': [],
        'combining_stages': [],
        'prime_implicants': [],
        'pi_chart': None,
        'essential_pis': [],
        'final_expression': '',
        'notes': []
    }

    if not minterms:
        steps['final_expression'] = '0'
        steps['notes'].append('No minterms → function is always 0 (contradiction)')
        return '0', steps

    if len(minterms) == 2 ** num_vars:
        steps['final_expression'] = '1'
        steps['notes'].append('All possible minterms present → function is always 1 (tautology)')
        return '1', steps

    bits = num_vars
    # Stage 0: list of minterms with binary
    mt_bin = {m: binary_repr(m, bits) for m in sorted(minterms)}
    steps['minterms'] = [{'decimal': m, 'binary': mt_bin[m]} for m in sorted(minterms)]

    # Group by number of 1s
    groups = defaultdict(list)
    for m, b in mt_bin.items():
        groups[count_ones(b)].append({'terms': (m,), 'bin': b, 'used': False})

    steps['grouping'] = [
        {'ones': k, 'items': [{'terms': list(it['terms']), 'bin': it['bin']} for it in v]}
        for k, v in sorted(groups.items())
    ]

    # Combining stages
    all_implicants = []
    current_groups = groups
    stage_num = 1

    while True:
        next_groups = defaultdict(list)
        used_pairs = set()
        stage_combos = []

        group_keys = sorted(current_groups.keys())
        for i in range(len(group_keys) - 1):
            g1 = group_keys[i]
            g2 = group_keys[i + 1]
            if g2 != g1 + 1:
                continue
            for a in current_groups[g1]:
                for b in current_groups[g2]:
                    combined = can_combine(a['bin'], b['bin'])
                    if combined:
                        new_terms = tuple(sorted(set(a['terms'] + b['terms'])))
                        key = (new_terms, combined)
                        if key not in used_pairs:
                            used_pairs.add(key)
                            next_groups[count_ones(combined.replace('-', ''))].append({
                                'terms': new_terms,
                                'bin': combined,
                                'used': False
                            })
                            a['used'] = True
                            b['used'] = True
                            stage_combos.append({
                                'from': [a['bin'], b['bin']],
                                'to': combined,
                                'decimals': list(new_terms)
                            })

        # Collect unused (prime implicants candidates)
        for g in current_groups.values():
            for item in g:
                if not item['used']:
                    all_implicants.append(item)

        steps['combining_stages'].append({
            'stage': stage_num,
            'combinations': stage_combos,
            'remaining_groups': {
                str(k): [{'terms': list(it['terms']), 'bin': it['bin']} for it in v]
                for k, v in sorted(next_groups.items())
            }
        })

        if not stage_combos:
            break

        current_groups = next_groups
        stage_num += 1
        if stage_num > 12:  # safety
            break

    # Also add leftover from last stage
    for g in current_groups.values():
        for item in g:
            if not item['used']:
                all_implicants.append(item)

    # Unique prime implicants
    seen = set()
    prime_implicants = []
    for pi in all_implicants:
        key = (pi['terms'], pi['bin'])
        if key not in seen:
            seen.add(key)
            prime_implicants.append(pi)

    steps['prime_implicants'] = [
        {
            'bin': pi['bin'],
            'terms': list(pi['terms']),
            'expr': term_to_expression(pi['bin'], var_names)
        }
        for pi in prime_implicants
    ]

    # Prime Implicant Chart
    chart = {}
    for pi in prime_implicants:
        chart[pi['bin']] = set(pi['terms'])

    # Essential PI selection (simple greedy + essentials)
    remaining_minterms = set(minterms)
    essential = []
    selected = []

    # Find essentials: columns with only one X
    while remaining_minterms:
        coverage_count = defaultdict(list)
        for bin_str, covered in chart.items():
            if bin_str in [e['bin'] for e in selected]:
                continue
            for m in covered:
                if m in remaining_minterms:
                    coverage_count[m].append(bin_str)

        # essentials
        found_essential = False
        for m, bins in coverage_count.items():
            if len(bins) == 1:
                chosen = bins[0]
                # find the pi
                for pi in prime_implicants:
                    if pi['bin'] == chosen and pi not in selected:
                        selected.append(pi)
                        essential.append(pi)
                        remaining_minterms -= set(pi['terms'])
                        found_essential = True
                        break
        if not found_essential:
            # pick the one that covers most remaining
            best = None
            best_cover = -1
            for pi in prime_implicants:
                if pi in selected:
                    continue
                cover = len(set(pi['terms']) & remaining_minterms)
                if cover > best_cover:
                    best_cover = cover
                    best = pi
            if best and best_cover > 0:
                selected.append(best)
                remaining_minterms -= set(best['terms'])
            else:
                break

    steps['essential_pis'] = [
        {'bin': pi['bin'], 'expr': term_to_expression(pi['bin'], var_names), 'terms': list(pi['terms'])}
        for pi in essential
    ]

    # Build PI chart data for frontend
    sorted_mts = sorted(minterms)
    pi_chart_rows = []
    for pi in prime_implicants:
        row = {
            'bin': pi['bin'],
            'expr': term_to_expression(pi['bin'], var_names),
            'marks': [('X' if m in pi['terms'] else '') for m in sorted_mts],
            'is_essential': pi in essential or pi in selected
        }
        pi_chart_rows.append(row)

    steps['pi_chart'] = {
        'minterms': sorted_mts,
        'rows': pi_chart_rows
    }

    # Final expression
    if not selected:
        # fallback – just OR all PIs (shouldn't happen often)
        selected = prime_implicants

    exprs = [term_to_expression(pi['bin'], var_names) for pi in selected]
    # remove duplicates while preserving order
    seen_e = set()
    unique_exprs = []
    for e in exprs:
        if e not in seen_e:
            seen_e.add(e)
            unique_exprs.append(e)

    final = ' | '.join(unique_exprs) if unique_exprs else '0'
    steps['final_expression'] = final
    steps['notes'].append(f"Selected {len(selected)} implicant(s) covering all minterms.")
    return final, steps


# -------------------------------------------------
#  Karnaugh Map
# -------------------------------------------------

def gray_code(n):
    """Return list of gray codes of bit length n."""
    if n <= 0:
        return ['']
    result = []
    for i in range(1 << n):
        gray = i ^ (i >> 1)
        result.append(format(gray, f'0{n}b'))
    return result


def build_kmap(minterms, var_names):
    """
    Build K-map structure for 2, 3 or 4 variables.
    Returns dict ready for frontend rendering.
    """
    n = len(var_names)
    if n < 2 or n > 4:
        return None

    minterm_set = set(minterms)

    if n == 2:
        # rows: A, cols: B
        row_vars = [var_names[0]]
        col_vars = [var_names[1]]
        row_labels = gray_code(1)
        col_labels = gray_code(1)
    elif n == 3:
        # rows: A, cols: BC
        row_vars = [var_names[0]]
        col_vars = var_names[1:]
        row_labels = gray_code(1)
        col_labels = gray_code(2)
    else:  # 4
        # rows: AB, cols: CD
        row_vars = var_names[:2]
        col_vars = var_names[2:]
        row_labels = gray_code(2)
        col_labels = gray_code(2)

    grid = []
    for r in row_labels:
        row = []
        for c in col_labels:
            # reconstruct the binary of the minterm
            full = r + c
            idx = int(full, 2)
            val = 1 if idx in minterm_set else 0
            row.append({'value': val, 'minterm': idx, 'bin': full})
        grid.append(row)

    return {
        'num_vars': n,
        'row_vars': row_vars,
        'col_vars': col_vars,
        'row_labels': row_labels,
        'col_labels': col_labels,
        'grid': grid,
        'var_names': var_names
    }


# -------------------------------------------------
#  Routes
# -------------------------------------------------

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/api/simplify', methods=['POST'])
def simplify():
    try:
        data = request.get_json()
        if not data or 'expression' not in data:
            return jsonify({'success': False, 'error': 'No expression given'}), 400

        expr_str = data['expression'].strip()
        if not expr_str:
            return jsonify({'success': False, 'error': 'Empty expression'}), 400

        form = data.get('form', 'auto')

        expr, var_names = parse_boolean_expression(expr_str)
        n_vars = len(var_names)

        # Minimal SOP (Sum of Products) and POS (Product of Sums)
        sop = simplify_logic(expr, form='dnf')   # minimal SOP
        pos = simplify_logic(expr, form='cnf')   # minimal POS
        # overall simplest (fewest terms / literals)
        simplified = simplify_logic(expr)

        # Truth table
        truth_table, tt_warning = generate_truth_table(expr, var_names)

        # Minterms + Quine-McCluskey
        minterms, _ = get_minterms(expr, var_names)
        qm_expr = None
        qm_steps = None
        kmap = None

        if 1 <= n_vars <= 6:
            qm_expr, qm_steps = quine_mccluskey(minterms, n_vars, var_names)
            if 2 <= n_vars <= 4:
                kmap = build_kmap(minterms, var_names)

        def pretty(e):
            s = str(e)
            s = s.replace('&', ' ∧ ').replace('|', ' ∨ ').replace('~', '¬')
            return s

        return jsonify({
            'success': True,
            'original': expr_str,
            'original_sympy': str(expr),
            'simplified': str(simplified),
            'simplified_pretty': pretty(simplified),
            'sop': str(sop),
            'sop_pretty': pretty(sop),
            'pos': str(pos),
            'pos_pretty': pretty(pos),
            'variables': var_names,
            'num_variables': n_vars,
            'minterms': minterms,
            'truth_table': truth_table,
            'truth_table_warning': tt_warning,
            'is_tautology': simplified == True,
            'is_contradiction': simplified == False,
            'quine_mccluskey': {
                'expression': qm_expr,
                'steps': qm_steps
            } if qm_steps else None,
            'kmap': kmap,
        })

    except ValueError as e:
        return jsonify({'success': False, 'error': str(e)}), 400
    except Exception as e:
        traceback.print_exc()
        return jsonify({'success': False, 'error': f'Server error: {str(e)}'}), 500


@app.route('/api/examples')
def examples():
    return jsonify({
        'examples': [
            {'name': 'Absorption law', 'expr': 'A | (A & B)'},
            {'name': 'De Morgan', 'expr': '~(A & B)'},
            {'name': 'XOR', 'expr': 'A ^ B'},
            {'name': 'Consensus', 'expr': '(A & B) | (~A & C) | (B & C)'},
            {'name': '3-variable', 'expr': '(~A & ~B & ~C) | (~A & B & ~C) | (A & ~B & C)'},
            {'name': 'Full adder carry', 'expr': '(A & B) | (B & Cin) | (A & Cin)'},
            {'name': 'Tautology', 'expr': 'A | ~A'},
            {'name': 'Contradiction', 'expr': 'A & ~A'},
            {'name': '4-var example', 'expr': '(A & B & ~C & ~D) | (A & ~B & C & ~D) | (~A & B & C & D)'},
            {'name': 'Simple SOP', 'expr': '(A & B) | (A & ~B) | (~A & B)'},
        ]
    })


if __name__ == '__main__':
    # debug True only while testing on local machine
    app.run(debug=True, host='0.0.0.0', port=5000)