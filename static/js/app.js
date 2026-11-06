/* frontend script - Boolean Simplifier
   NIRAJ VERMA | Scholar 319
*/

const $ = s => document.querySelector(s);
const $$ = s => document.querySelectorAll(s);

// navigation
$$('.navbtn').forEach(btn => {
    btn.addEventListener('click', () => {
        $$('.navbtn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        $$('.section').forEach(s => s.classList.remove('on'));
        $('#sec-' + btn.dataset.sec).classList.add('on');
    });
});

// quick tags
$$('.tag').forEach(t => {
    t.addEventListener('click', () => {
        $('#expr').value = t.dataset.e;
        $('#expr').focus();
    });
});

$('#btn-clear').addEventListener('click', () => {
    $('#expr').value = '';
    $('#out').style.display = 'none';
    $('#err').style.display = 'none';
});

// main simplify
async function doSimplify() {
    const expr = $('#expr').value.trim();
    if (!expr) {
        showErr('Please type an expression first.');
        return;
    }

    const form = 'auto';
    const btn = $('#btn-go');
    btn.disabled = true;
    btn.textContent = 'Working...';
    $('#err').style.display = 'none';

    try {
        const res = await fetch('/api/simplify', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ expression: expr, form })
        });
        const data = await res.json();

        if (!data.success) {
            showErr(data.error || 'Something went wrong');
            $('#out').style.display = 'none';
            return;
        }

        renderAll(data);
        $('#out').style.display = 'block';
    } catch (e) {
        showErr('Network / server error: ' + e.message);
        $('#out').style.display = 'none';
    } finally {
        btn.disabled = false;
        btn.textContent = 'Simplify →';
    }
}

$('#btn-go').addEventListener('click', doSimplify);
$('#expr').addEventListener('keydown', e => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
        e.preventDefault();
        doSimplify();
    }
});

function showErr(msg) {
    $('#err').textContent = msg;
    $('#err').style.display = 'block';
}

// ---------- render everything ----------
function renderAll(d) {
    // main result
    $('#res-main').textContent = d.simplified_pretty || d.simplified;

    let meta = '';
    meta += `<span class="badge">${d.num_variables} var${d.num_variables !== 1 ? 's' : ''}</span>`;
    if (d.variables && d.variables.length)
        meta += `<span class="badge">${d.variables.join(', ')}</span>`;
    if (d.minterms)
        meta += `<span class="badge">minterms: ${d.minterms.join(',') || 'none'}</span>`;
    if (d.is_tautology)
        meta += `<span class="badge ok">Tautology</span>`;
    if (d.is_contradiction)
        meta += `<span class="badge bad">Contradiction</span>`;
    $('#res-meta').innerHTML = meta;

    $('#res-sop').textContent = d.sop_pretty || d.sop;
    $('#res-pos').textContent = d.pos_pretty || d.pos;

    // K-map
    if (d.kmap) {
        $('#kmap-box').style.display = 'block';
        drawKmap(d.kmap);
    } else {
        $('#kmap-box').style.display = 'none';
    }

    // Quine-McCluskey steps
    if (d.quine_mccluskey && d.quine_mccluskey.steps) {
        $('#qm-box').style.display = 'block';
        drawQM(d.quine_mccluskey);
    } else {
        $('#qm-box').style.display = 'none';
    }

    // truth table
    if (d.truth_table) {
        $('#tt-box').style.display = 'block';
        $('#tt-warn').textContent = d.truth_table_warning || '';
        drawTT(d.truth_table);
    } else {
        $('#tt-box').style.display = 'none';
    }
}

// ----- K-map drawing -----
function drawKmap(km) {
    const area = $('#kmap-area');
    let html = '<table class="kmap-table">';

    // header row
    html += '<tr>';
    const cornerLabel = km.row_vars.join('') + '\\' + km.col_vars.join('');
    html += `<th class="kmap-corner">${cornerLabel}</th>`;
    km.col_labels.forEach(c => {
        html += `<th>${c}</th>`;
    });
    html += '</tr>';

    // data rows
    km.grid.forEach((row, ri) => {
        html += '<tr>';
        html += `<th>${km.row_labels[ri]}</th>`;
        row.forEach(cell => {
            const cls = cell.value === 1 ? 'one' : 'zero';
            html += `<td class="${cls}" title="m${cell.minterm}">${cell.value}</td>`;
        });
        html += '</tr>';
    });

    html += '</table>';
    area.innerHTML = html;
}

// ----- Quine-McCluskey steps -----
function drawQM(qm) {
    const steps = qm.steps;
    const box = $('#qm-steps');
    let html = '';

    // 1. minterms
    html += `<div class="qm-stage">
        <h4>Step 1 — List of Minterms</h4>
        <p>Minterms where function = 1:</p>
        <ul class="step-list">`;
    (steps.minterms || []).forEach(m => {
        html += `<li>m<sub>${m.decimal}</sub> = <code>${m.binary}</code></li>`;
    });
    html += '</ul></div>';

    // 2. initial grouping
    if (steps.grouping && steps.grouping.length) {
        html += `<div class="qm-stage">
            <h4>Step 2 — Group by number of 1s</h4>
            <table class="qm-table"><tr><th>No. of 1s</th><th>Minterms</th><th>Binary</th></tr>`;
        steps.grouping.forEach(g => {
            g.items.forEach((it, idx) => {
                html += `<tr>
                    ${idx === 0 ? `<td rowspan="${g.items.length}">${g.ones}</td>` : ''}
                    <td>${it.terms.join(', ')}</td>
                    <td><code>${it.bin}</code></td>
                </tr>`;
            });
        });
        html += '</table></div>';
    }

    // 3. combining stages
    (steps.combining_stages || []).forEach(st => {
        if (!st.combinations || !st.combinations.length) return;
        html += `<div class="qm-stage">
            <h4>Step 3.${st.stage} — Combining (stage ${st.stage})</h4>
            <p>Pairs that differ by one bit:</p>
            <ul class="step-list">`;
        st.combinations.forEach(c => {
            html += `<li><code>${c.from[0]}</code> + <code>${c.from[1]}</code> → <code>${c.to}</code>
                &nbsp;(minterms ${c.decimals.join(', ')})</li>`;
        });
        html += '</ul></div>';
    });

    // 4. prime implicants
    if (steps.prime_implicants && steps.prime_implicants.length) {
        html += `<div class="qm-stage">
            <h4>Step 4 — Prime Implicants</h4>
            <table class="qm-table">
            <tr><th>Binary</th><th>Minterms covered</th><th>Expression</th></tr>`;
        steps.prime_implicants.forEach(pi => {
            html += `<tr>
                <td><code>${pi.bin}</code></td>
                <td>${pi.terms.join(', ')}</td>
                <td><code>${pi.expr}</code></td>
            </tr>`;
        });
        html += '</table></div>';
    }

    // 5. PI chart
    if (steps.pi_chart) {
        const ch = steps.pi_chart;
        html += `<div class="qm-stage">
            <h4>Step 5 — Prime Implicant Chart</h4>
            <div style="overflow-x:auto">
            <table class="qm-table">
            <tr><th>PI \\ Minterm</th>`;
        ch.minterms.forEach(m => { html += `<th>m${m}</th>`; });
        html += '<th>Essential?</th></tr>';
        ch.rows.forEach(r => {
            const cls = r.is_essential ? 'essential' : '';
            html += `<tr class="${cls}"><td><code>${r.expr}</code></td>`;
            r.marks.forEach(mk => { html += `<td style="text-align:center">${mk}</td>`; });
            html += `<td style="text-align:center">${r.is_essential ? 'Yes' : ''}</td></tr>`;
        });
        html += '</table></div></div>';
    }

    // 6. essential + final
    html += `<div class="qm-stage">
        <h4>Step 6 — Essential Prime Implicants & Final Expression</h4>`;
    if (steps.essential_pis && steps.essential_pis.length) {
        html += '<p>Essential PIs:</p><ul class="step-list">';
        steps.essential_pis.forEach(e => {
            html += `<li><code>${e.expr}</code> (covers ${e.terms.join(', ')})</li>`;
        });
        html += '</ul>';
    }
    html += `<p style="margin-top:10px;"><strong>Final simplified expression (QM):</strong>
        <code style="font-size:1.05rem; color:var(--pink-dark);">${steps.final_expression}</code></p>`;
    (steps.notes || []).forEach(n => {
        html += `<p style="font-size:0.82rem;">${n}</p>`;
    });
    html += '</div>';

    box.innerHTML = html;
}

// ----- truth table -----
function drawTT(tt) {
    const thead = $('#ttable thead');
    const tbody = $('#ttable tbody');
    thead.innerHTML = '';
    tbody.innerHTML = '';

    const hr = document.createElement('tr');
    tt.header.forEach(h => {
        const th = document.createElement('th');
        th.textContent = h;
        hr.appendChild(th);
    });
    thead.appendChild(hr);

    tt.rows.forEach(row => {
        const tr = document.createElement('tr');
        row.forEach((v, i) => {
            const td = document.createElement('td');
            td.textContent = v;
            td.className = v === 1 ? 'one' : 'zero';
            tr.appendChild(td);
        });
        tbody.appendChild(tr);
    });
}

// load examples
async function loadEx() {
    try {
        const res = await fetch('/api/examples');
        const data = await res.json();
        const list = $('#ex-list');
        list.innerHTML = '';
        data.examples.forEach(ex => {
            const div = document.createElement('div');
            div.className = 'ex-item';
            div.innerHTML = `<span class="nm">${ex.name}</span><span class="ex">${ex.expr}</span>`;
            div.addEventListener('click', () => {
                $$('.navbtn').forEach(b => b.classList.remove('active'));
                $('[data-sec="simp"]').classList.add('active');
                $$('.section').forEach(s => s.classList.remove('on'));
                $('#sec-simp').classList.add('on');
                $('#expr').value = ex.expr;
                doSimplify();
            });
            list.appendChild(div);
        });
    } catch (e) {
        console.log('examples load failed', e);
    }
}

loadEx();
$('#expr').focus();