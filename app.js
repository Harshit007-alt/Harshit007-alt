// ============================================================
// CFG Derivation & Parse Tree Visualizer
// ============================================================

// ---- Constants ----
const EPSILON = 'ε';
const MAX_DEPTH = 30;
const MAX_ITERATIONS = 200000;

// ---- Example Grammars ----
const EXAMPLES = [
    {
        name: 'Balanced a\'s & b\'s',
        grammar: 'S -> aSb | ab',
        string: 'aaabbb'
    },
    {
        name: 'Arithmetic Expressions',
        grammar: 'E -> E+T | T\nT -> T*F | F\nF -> (E) | a',
        string: 'a+a*a'
    },
    {
        name: 'Balanced Parentheses',
        grammar: 'S -> (S)S | ε',
        string: '(())'
    },
    {
        name: 'Palindromes {a, b}',
        grammar: 'S -> aSa | bSb | a | b | ε',
        string: 'abba'
    },
    {
        name: 'Equal a\'s & b\'s',
        grammar: 'S -> aSb | bSa | SS | ε',
        string: 'abab'
    },
    {
        name: 'Strings with "aba"',
        grammar: 'S -> ASA\nA -> a | b | ε\nS -> aba',
        string: 'aabaa'
    },
    {
        name: 'Odd Length a\'s',
        grammar: 'S -> aaS | a',
        string: 'aaaaa'
    }
];

// ============================================================
// GRAMMAR PARSING
// ============================================================

function parseGrammar(input) {
    const lines = input.split('\n').map(l => l.trim()).filter(l => l.length > 0 && !l.startsWith('//'));
    if (lines.length === 0) {
        throw new Error('No grammar rules provided. Please enter at least one production rule.');
    }

    const rules = {};       // { NonTerminal: [ [sym1, sym2], [sym3], ... ] }
    const nonTerminals = new Set();
    const terminals = new Set();
    let startSymbol = null;

    for (const line of lines) {
        // Support ->, →, ::=, :=
        const match = line.match(/^(.+?)\s*(?:->|→|::=|:=)\s*(.+)$/);
        if (!match) {
            throw new Error(`Invalid rule format: "${line}". Use format: S -> aB | bA`);
        }

        const lhs = match[1].trim();
        const rhsStr = match[2].trim();

        if (lhs.length === 0) {
            throw new Error(`Empty left-hand side in rule: "${line}"`);
        }

        // Validate LHS is a single uppercase letter
        if (!/^[A-Z]$/.test(lhs)) {
            throw new Error(`Non-terminal "${lhs}" must be a single uppercase letter (A-Z).`);
        }

        nonTerminals.add(lhs);
        if (startSymbol === null) {
            startSymbol = lhs;
        }

        // Split alternatives by |
        const alternatives = rhsStr.split('|').map(a => a.trim());
        if (!rules[lhs]) rules[lhs] = [];

        for (const alt of alternatives) {
            if (alt.length === 0) {
                throw new Error(`Empty alternative in rule for ${lhs}.`);
            }
            const production = tokenizeProduction(alt);
            rules[lhs].push(production);
        }
    }

    // Identify terminals
    for (const nt of Object.keys(rules)) {
        for (const prod of rules[nt]) {
            for (const sym of prod) {
                if (sym !== EPSILON && !nonTerminals.has(sym)) {
                    terminals.add(sym);
                }
            }
        }
    }

    return { rules, nonTerminals, terminals, startSymbol };
}

function tokenizeProduction(str) {
    str = str.trim();

    // Handle epsilon variants
    if (str === EPSILON || str === 'ε' || str === 'ϵ' || str.toLowerCase() === 'epsilon' ||
        str.toLowerCase() === 'lambda' || str === 'λ' || str === '#') {
        return [];  // Empty production
    }

    const symbols = [];
    for (let i = 0; i < str.length; i++) {
        const ch = str[i];
        if (ch === ' ' || ch === '\t') continue;  // Skip whitespace
        if (ch === 'ε' || ch === 'ϵ') {
            // Epsilon as part of a longer string - treat as standalone
            // Actually this shouldn't happen if ε is alone, but handle anyway
            continue;
        }
        symbols.push(ch);
    }

    return symbols;
}

// ============================================================
// MIN-LENGTH COMPUTATION
// ============================================================

function computeMinLengths(rules, nonTerminals) {
    const minLen = {};
    for (const nt of nonTerminals) {
        minLen[nt] = Infinity;
    }

    let changed = true;
    while (changed) {
        changed = false;
        for (const nt of nonTerminals) {
            for (const prod of (rules[nt] || [])) {
                let len = 0;
                let possible = true;
                for (const sym of prod) {
                    if (nonTerminals.has(sym)) {
                        if (minLen[sym] === Infinity) {
                            possible = false;
                            break;
                        }
                        len += minLen[sym];
                    } else {
                        len += 1;
                    }
                }
                if (possible && len < minLen[nt]) {
                    minLen[nt] = len;
                    changed = true;
                }
            }
        }
    }

    return minLen;
}

// ============================================================
// DERIVATION ENGINE
// ============================================================

function findDerivation(grammar, startSymbol, target, nonTerminals, type, minLengths) {
    const { rules } = grammar;
    let found = null;
    let iterations = 0;
    const visited = new Set();
    const startTime = Date.now();
    const TIME_LIMIT = 5000; // 5 seconds max
    let timedOut = false;

    // Check if min-length of start symbol exceeds target
    if (minLengths[startSymbol] > target.length) {
        return { result: null, timedOut: false };
    }

    // Compute minimum possible length of a sentential form
    function getMinTotalLength(form) {
        let len = 0;
        for (const s of form) {
            if (nonTerminals.has(s)) {
                const ml = minLengths[s];
                if (ml === Infinity) return Infinity;
                len += ml;
            } else {
                len += 1;
            }
        }
        return len;
    }

    function getTerminalCount(form) {
        let count = 0;
        for (const s of form) {
            if (!nonTerminals.has(s)) count++;
        }
        return count;
    }

    function getPrefix(form) {
        let prefix = '';
        for (const s of form) {
            if (nonTerminals.has(s)) break;
            prefix += s;
        }
        return prefix;
    }

    function getSuffix(form) {
        let suffix = '';
        for (let i = form.length - 1; i >= 0; i--) {
            if (nonTerminals.has(form[i])) break;
            suffix = form[i] + suffix;
        }
        return suffix;
    }

    // Check all terminal segments between non-terminals match the target
    function checkTerminalSegments(form) {
        let pos = 0; // position in target being consumed
        let i = 0;
        while (i < form.length) {
            if (nonTerminals.has(form[i])) {
                // Skip non-terminal, consume at least minLen chars from target
                pos += minLengths[form[i]];
                if (pos > target.length) return false;
                i++;
            } else {
                // Collect terminal segment
                let seg = '';
                while (i < form.length && !nonTerminals.has(form[i])) {
                    seg += form[i];
                    i++;
                }
                // Check if this segment matches target at current pos
                if (pos + seg.length > target.length) return false;
                if (target.substring(pos, pos + seg.length) !== seg) return false;
                pos += seg.length;
            }
        }
        return true;
    }

    function dfs(form, history, depth) {
        if (found || iterations > MAX_ITERATIONS) return;
        if (Date.now() - startTime > TIME_LIMIT) {
            timedOut = true;
            return;
        }
        iterations++;

        // Create a key for cycle detection
        const formKey = form.join('\u0000');
        if (visited.has(formKey)) return;
        visited.add(formKey);

        // Find non-terminal to expand
        let ntIndex = -1;
        if (type === 'leftmost') {
            ntIndex = form.findIndex(s => nonTerminals.has(s));
        } else {
            for (let i = form.length - 1; i >= 0; i--) {
                if (nonTerminals.has(form[i])) {
                    ntIndex = i;
                    break;
                }
            }
        }

        // No non-terminals left
        if (ntIndex === -1) {
            if (form.join('') === target) {
                found = history.map(h => ({ ...h }));
            }
            return;
        }

        if (depth >= MAX_DEPTH) return;

        const nt = form[ntIndex];
        const productions = rules[nt] || [];

        for (const prod of productions) {
            if (found || timedOut) return;

            const newForm = [...form.slice(0, ntIndex), ...prod, ...form.slice(ntIndex + 1)];

            // Pruning 1: min total length exceeds target
            const minTotal = getMinTotalLength(newForm);
            if (minTotal > target.length) continue;

            // Pruning 2: terminal count exceeds target
            const termCount = getTerminalCount(newForm);
            if (termCount > target.length) continue;

            // Pruning 3: if all terminals, length must match exactly
            const hasNT = newForm.some(s => nonTerminals.has(s));
            if (!hasNT && termCount !== target.length) continue;

            // Pruning 4: prefix match
            const prefix = getPrefix(newForm);
            if (prefix.length > 0 && !target.startsWith(prefix)) continue;

            // Pruning 5: suffix match
            const suffix = getSuffix(newForm);
            if (suffix.length > 0 && !target.endsWith(suffix)) continue;

            // Pruning 6: prefix+suffix overlap (only with NTs present)
            if (hasNT && prefix.length + suffix.length > target.length) continue;

            // Pruning 7: for leftmost derivation, all terminals to the left are fixed,
            // so we can do full segment checking
            if (type === 'leftmost' && !checkTerminalSegments(newForm)) continue;

            history.push({
                prevForm: [...form],
                newForm: [...newForm],
                expandedIndex: ntIndex,
                production: [...prod],
                nt: nt
            });

            dfs(newForm, history, depth + 1);

            if (!found) {
                history.pop();
            }
        }

        // Allow revisiting this form via different paths
        visited.delete(formKey);
    }

    dfs([startSymbol], [], 0);
    return { result: found, timedOut };
}

// ============================================================
// PARSE TREE BUILDER
// ============================================================

class TreeNode {
    constructor(symbol, isTerminal = false) {
        this.symbol = symbol;
        this.isTerminal = isTerminal;
        this.children = [];
        this.step = 0; // derivation step at which this node appears
        // Layout properties
        this.x = 0;
        this.y = 0;
        this.subtreeWidth = 0;
    }
}

function buildParseTree(startSymbol, derivationHistory, nonTerminals, stepLimit = Infinity) {
    const root = new TreeNode(startSymbol, false);
    root.step = 0;
    let leaves = [root];

    for (let i = 0; i < Math.min(derivationHistory.length, stepLimit); i++) {
        const step = derivationHistory[i];
        const { expandedIndex, production, nt } = step;

        const node = leaves[expandedIndex];
        if (!node) continue;

        if (production.length === 0) {
            const epsilonChild = new TreeNode(EPSILON, true);
            epsilonChild.step = i + 1;
            node.children = [epsilonChild];
            leaves.splice(expandedIndex, 1);
        } else {
            const children = production.map(sym => {
                const child = new TreeNode(sym, !nonTerminals.has(sym));
                child.step = i + 1;
                return child;
            });
            node.children = children;
            leaves.splice(expandedIndex, 1, ...children);
        }
    }

    return root;
}

// ============================================================
// TREE LAYOUT
// ============================================================

const NODE_RADIUS = 22;
const LEVEL_HEIGHT = 75;
const MIN_NODE_WIDTH = 55;
const SIBLING_SPACING = 10;

function calculateSubtreeWidth(node) {
    if (node.children.length === 0) {
        node.subtreeWidth = MIN_NODE_WIDTH;
        return;
    }

    for (const child of node.children) {
        calculateSubtreeWidth(child);
    }

    const totalChildWidth = node.children.reduce((sum, c) => sum + c.subtreeWidth, 0);
    const gaps = (node.children.length - 1) * SIBLING_SPACING;
    node.subtreeWidth = Math.max(totalChildWidth + gaps, MIN_NODE_WIDTH);
}

function assignPositions(node, centerX, y) {
    node.x = centerX;
    node.y = y;

    if (node.children.length === 0) return;

    const totalChildWidth = node.children.reduce((sum, c) => sum + c.subtreeWidth, 0);
    const gaps = (node.children.length - 1) * SIBLING_SPACING;
    const totalWidth = totalChildWidth + gaps;

    let currentX = centerX - totalWidth / 2;

    for (const child of node.children) {
        const childCenterX = currentX + child.subtreeWidth / 2;
        assignPositions(child, childCenterX, y + LEVEL_HEIGHT);
        currentX += child.subtreeWidth + SIBLING_SPACING;
    }
}

function layoutTree(root) {
    calculateSubtreeWidth(root);
    const centerX = root.subtreeWidth / 2;
    assignPositions(root, centerX, NODE_RADIUS + 20);
}

// ============================================================
// SVG RENDERING
// ============================================================

function renderTreeSVG(root, container) {
    layoutTree(root);

    // Calculate SVG dimensions
    let maxX = 0, maxY = 0;
    function findBounds(node) {
        maxX = Math.max(maxX, node.x + NODE_RADIUS);
        maxY = Math.max(maxY, node.y + NODE_RADIUS);
        for (const child of node.children) {
            findBounds(child);
        }
    }
    findBounds(root);

    const svgWidth = maxX + NODE_RADIUS + 40;
    const svgHeight = maxY + NODE_RADIUS + 40;

    const NS = 'http://www.w3.org/2000/svg';
    const svg = document.createElementNS(NS, 'svg');
    svg.setAttribute('width', svgWidth);
    svg.setAttribute('height', svgHeight);
    svg.setAttribute('viewBox', `0 0 ${svgWidth} ${svgHeight}`);

    // Defs for gradients and filters
    const defs = document.createElementNS(NS, 'defs');

    // Node gradient for non-terminals
    const ntGrad = document.createElementNS(NS, 'radialGradient');
    ntGrad.setAttribute('id', 'ntNodeGrad');
    const stop1 = document.createElementNS(NS, 'stop');
    stop1.setAttribute('offset', '0%');
    stop1.setAttribute('style', 'stop-color:rgba(124,108,240,0.35)');
    const stop2 = document.createElementNS(NS, 'stop');
    stop2.setAttribute('offset', '100%');
    stop2.setAttribute('style', 'stop-color:rgba(124,108,240,0.1)');
    ntGrad.appendChild(stop1);
    ntGrad.appendChild(stop2);
    defs.appendChild(ntGrad);

    // Terminal gradient
    const tGrad = document.createElementNS(NS, 'radialGradient');
    tGrad.setAttribute('id', 'tNodeGrad');
    const ts1 = document.createElementNS(NS, 'stop');
    ts1.setAttribute('offset', '0%');
    ts1.setAttribute('style', 'stop-color:rgba(0,212,200,0.3)');
    const ts2 = document.createElementNS(NS, 'stop');
    ts2.setAttribute('offset', '100%');
    ts2.setAttribute('style', 'stop-color:rgba(0,212,200,0.08)');
    tGrad.appendChild(ts1);
    tGrad.appendChild(ts2);
    defs.appendChild(tGrad);

    // Glow filter
    const filter = document.createElementNS(NS, 'filter');
    filter.setAttribute('id', 'glow');
    filter.setAttribute('x', '-50%');
    filter.setAttribute('y', '-50%');
    filter.setAttribute('width', '200%');
    filter.setAttribute('height', '200%');
    const feGauss = document.createElementNS(NS, 'feGaussianBlur');
    feGauss.setAttribute('stdDeviation', '3');
    feGauss.setAttribute('result', 'coloredBlur');
    filter.appendChild(feGauss);
    const feMerge = document.createElementNS(NS, 'feMerge');
    const feMergeNode1 = document.createElementNS(NS, 'feMergeNode');
    feMergeNode1.setAttribute('in', 'coloredBlur');
    const feMergeNode2 = document.createElementNS(NS, 'feMergeNode');
    feMergeNode2.setAttribute('in', 'SourceGraphic');
    feMerge.appendChild(feMergeNode1);
    feMerge.appendChild(feMergeNode2);
    filter.appendChild(feMerge);
    defs.appendChild(filter);

    svg.appendChild(defs);

    // Edges group (draw first, behind nodes)
    const edgesGroup = document.createElementNS(NS, 'g');
    edgesGroup.setAttribute('class', 'edges-group');

    // Nodes group
    const nodesGroup = document.createElementNS(NS, 'g');
    nodesGroup.setAttribute('class', 'nodes-group');

    let animDelay = 0;
    const ANIM_STEP = 0.08;

    function renderNode(node, parent = null) {
        const stepNum = node.step;

        // Draw edge from parent to this node
        if (parent) {
            const line = document.createElementNS(NS, 'line');
            line.setAttribute('x1', parent.x);
            line.setAttribute('y1', parent.y);
            line.setAttribute('x2', node.x);
            line.setAttribute('y2', node.y);
            line.setAttribute('class', 'tree-edge');
            line.setAttribute('data-step', stepNum);
            line.style.opacity = '0';
            line.style.transition = 'opacity 0.4s var(--ease)';
            edgesGroup.appendChild(line);
        }

        // Node circle
        const isEpsilon = node.symbol === EPSILON;
        const circle = document.createElementNS(NS, 'circle');
        circle.setAttribute('cx', node.x);
        circle.setAttribute('cy', node.y);
        circle.setAttribute('r', NODE_RADIUS);
        circle.setAttribute('class', 'tree-node-circle');

        if (node.isTerminal) {
            circle.setAttribute('fill', isEpsilon ? 'rgba(92,92,128,0.15)' : 'url(#tNodeGrad)');
            circle.setAttribute('stroke', isEpsilon ? 'rgba(92,92,128,0.3)' : 'rgba(0,212,200,0.5)');
        } else {
            circle.setAttribute('fill', 'url(#ntNodeGrad)');
            circle.setAttribute('stroke', 'rgba(124,108,240,0.5)');
        }
        circle.setAttribute('stroke-width', '1.5');
        circle.setAttribute('filter', 'url(#glow)');

        const g = document.createElementNS(NS, 'g');
        g.setAttribute('data-step', stepNum);
        g.style.opacity = '0';
        g.style.transition = 'opacity 0.4s var(--ease)';
        g.appendChild(circle);

        // Label
        const text = document.createElementNS(NS, 'text');
        text.setAttribute('x', node.x);
        text.setAttribute('y', node.y);
        let labelClass = 'tree-label';
        if (node.isTerminal) labelClass += isEpsilon ? ' tree-label-epsilon' : ' tree-label-terminal';
        text.setAttribute('class', labelClass);
        text.textContent = node.symbol;

        g.appendChild(text);
        nodesGroup.appendChild(g);

        for (const child of node.children) {
            renderNode(child, node);
        }
    }

    renderNode(root);
    svg.appendChild(edgesGroup);
    svg.appendChild(nodesGroup);

    container.innerHTML = '';
    container.appendChild(svg);
    
    // Auto-scale to fit
    setTimeout(autoScaleTree, 50);

    // Show step 0 (just root) by default
    revealTreeStep(0);
}

function autoScaleTree() {
    const viewport = document.getElementById('tree-viewport');
    const canvas = document.getElementById('tree-canvas');
    const svg = canvas.querySelector('svg');
    if (!svg || !viewport) return;

    const vw = viewport.clientWidth - 80;
    const vh = viewport.clientHeight - 80; 
    const sw = parseFloat(svg.getAttribute('width')) || 1000;
    const sh = parseFloat(svg.getAttribute('height')) || 1000;

    // Calculate scale factor to fit the tree within the viewport
    const scaleX = vw / sw;
    const scaleY = vh / sh;
    const scale = Math.min(scaleX, scaleY);
    
    currentZoom = Math.max(scale * 0.95, 0.2); 
    
    // Reset pan so it starts centered at the top
    canvas.style.transform = `translate(0px, 0px) scale(${currentZoom})`;
}

// Reveal all nodes/edges up to stepNum without re-rendering
function revealTreeStep(stepNum) {
    const svg = document.querySelector('#tree-canvas svg');
    if (!svg) return;

    // Show nodes/edges up to this step
    svg.querySelectorAll('[data-step]').forEach(el => {
        const s = parseInt(el.getAttribute('data-step'));
        el.style.opacity = s <= stepNum ? '1' : '0';
    });

    // Update rule display
    const ruleDisplay = document.getElementById('tree-rule-display');
    const derivation = leftmostResult || rightmostResult;
    
    if (stepNum > 0 && derivation && derivation[stepNum - 1]) {
        const step = derivation[stepNum - 1];
        const prodStr = step.production.length > 0 ? step.production.join('') : EPSILON;
        ruleDisplay.innerHTML = `<span style="color:var(--text-muted); font-size: 0.7rem; display:block; margin-bottom: 2px;">Step ${stepNum}</span> ${step.nt} → ${prodStr}`;
        ruleDisplay.classList.add('active');
    } else {
        ruleDisplay.classList.remove('active');
    }

    // Automatically fit to window
    autoScaleTree();
}

// ============================================================
// DERIVATION DISPLAY
// ============================================================

function formatSententialForm(form, nonTerminals, highlightIndex = -1, highlightLen = 0, highlightType = '') {
    const span = document.createElement('span');
    span.className = 'step-form';

    for (let i = 0; i < form.length; i++) {
        const sym = form[i];
        const s = document.createElement('span');
        s.textContent = sym;

        if (highlightType === 'expanded' && i === highlightIndex) {
            s.className = 'sym-expanded';
        } else if (highlightType === 'result' && i >= highlightIndex && i < highlightIndex + highlightLen) {
            s.className = 'sym-result';
        } else if (nonTerminals.has(sym)) {
            s.className = 'sym-nt';
        } else {
            s.className = 'sym-t';
        }

        span.appendChild(s);
    }

    if (form.length === 0) {
        const s = document.createElement('span');
        s.textContent = EPSILON;
        s.className = 'sym-t';
        span.appendChild(s);
    }

    return span;
}

function displayDerivation(history, startSymbol, container, nonTerminals, type) {
    container.innerHTML = '';

    if (!history || history.length === 0) {
        container.innerHTML = `
            <div class="derivation-container">
                <div class="no-derivation">
                    <span class="no-icon">🔍</span>
                    <div class="no-title">No ${type} derivation found</div>
                    <div class="no-desc">The string cannot be derived from this grammar using ${type.toLowerCase()} derivation. Verify that your string belongs to the language generated by the grammar.</div>
                </div>
            </div>`;
        return;
    }

    const wrapper = document.createElement('div');
    wrapper.className = 'derivation-container';

    // Title
    const title = document.createElement('div');
    title.className = 'derivation-title';
    title.innerHTML = `${type === 'Leftmost' ? '⬅️' : '➡️'} ${type} Derivation <span class="step-count">${history.length} steps</span>`;
    wrapper.appendChild(title);

    const stepList = document.createElement('div');
    stepList.className = 'step-list';

    // Initial step: just the start symbol
    const initStep = document.createElement('div');
    initStep.className = 'derivation-step';
    initStep.style.animationDelay = '0s';

    const initNum = document.createElement('span');
    initNum.className = 'step-number';
    initNum.textContent = '0';
    initStep.appendChild(initNum);

    const initForm = formatSententialForm([startSymbol], nonTerminals);
    initStep.appendChild(initForm);
    stepList.appendChild(initStep);

    // Each derivation step
    history.forEach((step, i) => {
        const stepDiv = document.createElement('div');
        stepDiv.className = 'derivation-step';
        stepDiv.style.animationDelay = `${(i + 1) * 0.06}s`;

        // Step number
        const num = document.createElement('span');
        num.className = 'step-number';
        num.textContent = String(i + 1);
        stepDiv.appendChild(num);

        // Previous form with highlighted non-terminal
        const prevForm = formatSententialForm(step.prevForm, nonTerminals, step.expandedIndex, 1, 'expanded');
        stepDiv.appendChild(prevForm);

        // Arrow
        const arrow = document.createElement('span');
        arrow.className = 'step-arrow';
        arrow.textContent = '⇒';
        stepDiv.appendChild(arrow);

        // New form with highlighted result
        const prodLen = step.production.length;
        const newForm = formatSententialForm(step.newForm, nonTerminals, step.expandedIndex, prodLen, 'result');
        stepDiv.appendChild(newForm);

        // Rule used
        const ruleSpan = document.createElement('span');
        ruleSpan.className = 'step-rule';
        const prodStr = step.production.length > 0 ? step.production.join('') : EPSILON;
        ruleSpan.textContent = `${step.nt} → ${prodStr}`;
        stepDiv.appendChild(ruleSpan);

        stepList.appendChild(stepDiv);

        // Click to visualize this step in the tree
        stepDiv.addEventListener('click', () => {
            // Update active state across ALL derivation panels
            document.querySelectorAll('.derivation-step').forEach(s => s.classList.remove('active'));
            stepDiv.classList.add('active');

            // Sync the keyboard step tracker
            currentStepIndex = i + 1;

            // Reveal tree up to this step (no re-render)
            revealTreeStep(i + 1);
            
            // Auto-switch to parse tree tab
            switchTab('parse-tree');
        });
    });

    wrapper.appendChild(stepList);
    container.appendChild(wrapper);
}

// ============================================================
// UI CONTROLLER
// ============================================================

let currentZoom = 1;
let leftmostResult = null;
let rightmostResult = null;
let parseTreeRoot = null;
let currentGrammarInfo = null;
let currentStepIndex = -1; // Track keyboard stepping through derivation

function showError(msg) {
    const banner = document.getElementById('error-banner');
    const text = document.getElementById('error-text');
    text.textContent = msg;
    banner.style.display = 'flex';
}

function hideError() {
    document.getElementById('error-banner').style.display = 'none';
}

function switchTab(tabName) {
    // Update tab buttons
    document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
    document.querySelector(`.tab[data-tab="${tabName}"]`).classList.add('active');

    // Update panels
    document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
    document.getElementById(`panel-${tabName}`).classList.add('active');

    // Render parse tree on first view
    if (tabName === 'parse-tree' && parseTreeRoot) {
        const canvas = document.getElementById('tree-canvas');
        if (canvas.children.length === 0) {
            renderTreeSVG(parseTreeRoot, canvas);
        }
    }
}

function handleGenerate() {
    hideError();

    const grammarInput = document.getElementById('grammar-input').value.trim();
    let targetString = document.getElementById('string-input').value.trim();

    // Handle epsilon as target
    if (targetString === EPSILON || targetString === 'ε' || targetString === 'ϵ' ||
        targetString.toLowerCase() === 'epsilon' || targetString.toLowerCase() === 'lambda' || targetString === 'λ') {
        targetString = '';
    }

    if (!grammarInput) {
        showError('Please enter grammar rules.');
        return;
    }

    // Parse grammar
    let grammar;
    try {
        grammar = parseGrammar(grammarInput);
    } catch (e) {
        showError(e.message);
        return;
    }

    // Validate target string contains only terminals
    for (const ch of targetString) {
        if (grammar.nonTerminals.has(ch)) {
            showError(`Character "${ch}" in the input string is a non-terminal. The string should only contain terminal symbols.`);
            return;
        }
    }

    // Show loading
    const resultsSection = document.getElementById('results-section');
    resultsSection.style.display = 'block';

    const leftPanel = document.getElementById('panel-leftmost');
    const rightPanel = document.getElementById('panel-rightmost');
    const treeCanvas = document.getElementById('tree-canvas');

    leftPanel.innerHTML = '<div class="loading-container"><div class="spinner"></div><div class="loading-text">Computing leftmost derivation...</div></div>';
    rightPanel.innerHTML = '<div class="loading-container"><div class="spinner"></div><div class="loading-text">Computing rightmost derivation...</div></div>';
    treeCanvas.innerHTML = '';
    document.getElementById('tree-rule-display').classList.remove('active');

    // Update grammar info
    const infoEl = document.getElementById('grammar-info');
    const termStr = [...grammar.terminals].join(', ') || 'none';
    const ntStr = [...grammar.nonTerminals].join(', ');
    infoEl.textContent = `Start: ${grammar.startSymbol} | NT: {${ntStr}} | T: {${termStr}}`;
    currentGrammarInfo = grammar;

    // Reset zoom
    currentZoom = 1;
    currentStepIndex = -1; // Reset keyboard step tracker
    treeCanvas.style.transform = `translate(0px, 0px) scale(${currentZoom})`;

    // Switch to leftmost tab
    switchTab('leftmost');

    // Compute minimum derivation lengths for pruning
    const minLengths = computeMinLengths(grammar.rules, grammar.nonTerminals);

    // Use setTimeout to allow UI update before heavy computation
    setTimeout(() => {
        // Find leftmost derivation
        const leftRes = findDerivation(grammar, grammar.startSymbol, targetString, grammar.nonTerminals, 'leftmost', minLengths);
        leftmostResult = leftRes.result;
        displayDerivation(leftmostResult, grammar.startSymbol, leftPanel, grammar.nonTerminals, 'Leftmost');

        // Find rightmost derivation
        const rightRes = findDerivation(grammar, grammar.startSymbol, targetString, grammar.nonTerminals, 'rightmost', minLengths);
        rightmostResult = rightRes.result;
        displayDerivation(rightmostResult, grammar.startSymbol, rightPanel, grammar.nonTerminals, 'Rightmost');

        // Build parse tree from leftmost derivation (if found)
        parseTreeRoot = null;
        const derivationForTree = leftmostResult || rightmostResult;
        if (derivationForTree) {
            // Build the FULL tree (all steps)
            parseTreeRoot = buildParseTree(grammar.startSymbol, derivationForTree, grammar.nonTerminals);
            // Render the full SVG once (nodes hidden beyond step 0)
            renderTreeSVG(parseTreeRoot, treeCanvas);
        } else {
            treeCanvas.innerHTML = `
                <div class="no-derivation" style="width:100%;">
                    <span class="no-icon">🌳</span>
                    <div class="no-title">No parse tree available</div>
                    <div class="no-desc">A parse tree can only be generated if a derivation is found.</div>
                </div>`;
        }
    }, 50);
}

function loadExample(index) {
    const ex = EXAMPLES[index];
    if (!ex) return;
    document.getElementById('grammar-input').value = ex.grammar;
    document.getElementById('string-input').value = ex.string;

    // Close dropdown
    const menu = document.getElementById('examples-menu');
    if (menu) menu.classList.remove('open');
}



// ---- Symbol Insertion ----
function insertSymbol(symbol) {
    const input = document.getElementById('grammar-input');
    const start = input.selectionStart;
    const end = input.selectionEnd;
    const text = input.value;
    
    // Add spaces around arrow and pipe for better formatting
    let content = symbol;
    if (symbol === '->') content = ' -> ';
    if (symbol === '|') content = ' | ';
    
    const before = text.substring(0, start);
    const after = text.substring(end, text.length);
    
    input.value = before + content + after;
    input.focus();
    input.selectionStart = input.selectionEnd = start + content.length;
}

// ---- Random Example Generator ----
const GRAMMAR_TEMPLATES = [
    {
        name: "Nested Brackets",
        rules: "S -> [S] | {S} | (S) | ε",
        terminals: ["[", "]", "{", "}", "(", ")"]
    },
    {
        name: "Alternating Bits",
        rules: "S -> 01S | 10S | ε",
        terminals: ["0", "1"]
    },
    {
        name: "Repeated Blocks",
        rules: "S -> abS | cdS | ε",
        terminals: ["a", "b", "c", "d"]
    }
];

function generateRandomString(rules, startSymbol, nonTerminals, maxLen = 8) {
    let current = [startSymbol];
    let steps = 0;
    
    while (steps < 20) {
        const ntIndices = current.map((s, i) => nonTerminals.has(s) ? i : -1).filter(i => i !== -1);
        if (ntIndices.length === 0) break;
        
        // Pick far left non-terminal
        const idx = ntIndices[0];
        const nt = current[idx];
        const prods = rules[nt];
        
        // Pick a random production
        let filteredProds = prods;
        const currentLen = current.length;
        
        if (currentLen < 3) {
            filteredProds = prods.filter(p => p.length > 0);
        } else if (currentLen > maxLen) {
            filteredProds = prods.filter(p => p.length === 0 || p.every(s => !nonTerminals.has(s)));
        }
        
        if (filteredProds.length === 0) filteredProds = prods;
        
        const randomProd = filteredProds[Math.floor(Math.random() * filteredProds.length)];
        current.splice(idx, 1, ...randomProd);
        steps++;
    }
    
    return current.join('');
}

function handleRandomExample() {
    const template = GRAMMAR_TEMPLATES[Math.floor(Math.random() * GRAMMAR_TEMPLATES.length)];
    const parsed = parseGrammar(template.rules);
    const randomStr = generateRandomString(parsed.rules, parsed.startSymbol, parsed.nonTerminals);
    
    document.getElementById('grammar-input').value = template.rules;
    document.getElementById('string-input').value = randomStr || EPSILON;
    
    // Trigger generate
    handleGenerate();
    
    // Close menu
    document.getElementById('examples-menu').classList.remove('open');
}

// ============================================================
// INTERACTIVE TOUR (SPOTLIGHT)
// ============================================================

let tourIndex = 0;
let tourActive = false;

const TOUR_STEPS = [
    {
        title: "Welcome! 👋",
        desc: "Let's take a quick tour of this CFG Visualizer. You'll be a pro in under a minute!",
        target: null // No target, centered
    },
    {
        title: "Grammar Rules 📝",
        desc: "Type your production rules here. Use the format S -> aS | b. One rule per line.",
        target: "grammar-input"
    },
    {
        title: "Symbol Shortcuts ⚡",
        desc: "Click these buttons to quickly insert ε, →, or | at your cursor position.",
        target: "symbol-buttons"
    },
    {
        title: "Target String 🎯",
        desc: "Enter the string you want to derive from the grammar. Try 'aab' or load an example!",
        target: "string-input"
    },
    {
        title: "Generate! 🚀",
        desc: "Hit this button to compute both leftmost and rightmost derivations automatically.",
        target: "generate-btn"
    },
    {
        title: "Step-by-Step 🌳",
        desc: "After generating, click any derivation step to watch the parse tree grow branch by branch. Or press Enter repeatedly!",
        target: "results-section"
    },
    {
        title: "You're Ready! 🎉",
        desc: "That's it! Load an example, generate derivations, and explore the parse tree. Have fun mastering CFGs!",
        target: null
    }
];

function startTour() {
    tourIndex = 0;
    tourActive = true;
    document.getElementById('tour-backdrop').classList.add('active');
    document.getElementById('tour-tooltip').classList.add('active');
    showTourStep();
}

function endTour() {
    tourActive = false;
    document.getElementById('tour-backdrop').classList.remove('active');
    document.getElementById('tour-tooltip').classList.remove('active');
}

function showTourStep() {
    const step = TOUR_STEPS[tourIndex];
    if (!step) { endTour(); return; }

    const total = TOUR_STEPS.length;

    // Update content
    document.getElementById('tour-title').textContent = step.title;
    document.getElementById('tour-desc').textContent = step.desc;
    document.getElementById('tour-step-badge').textContent = `Step ${tourIndex + 1} of ${total}`;
    document.getElementById('tour-progress-bar').style.width = `${((tourIndex + 1) / total) * 100}%`;

    // Button states
    document.getElementById('tour-prev').style.display = tourIndex === 0 ? 'none' : 'inline-flex';
    document.getElementById('tour-next').textContent = tourIndex === total - 1 ? 'Finish 🎉' : 'Next →';

    // Position tooltip
    const tooltip = document.getElementById('tour-tooltip');
    const targetEl = step.target ? document.getElementById(step.target) : null;

    if (targetEl) {
        // Scroll the target into view first
        targetEl.scrollIntoView({ behavior: 'smooth', block: 'center' });

        // Use requestAnimationFrame to wait for scroll to settle
        requestAnimationFrame(() => {
            setTimeout(() => {
                const rect = targetEl.getBoundingClientRect();
                const tooltipH = tooltip.offsetHeight || 280;
                const tooltipW = 360;

                // Try below target
                let top = rect.bottom + 12;
                let left = rect.left + rect.width / 2 - tooltipW / 2;

                // If tooltip goes off bottom, place above
                if (top + tooltipH > window.innerHeight - 10) {
                    top = rect.top - tooltipH - 12;
                }
                // If still off top, just center vertically
                if (top < 10) {
                    top = Math.max(10, (window.innerHeight - tooltipH) / 2);
                }

                // Horizontal bounds
                left = Math.max(12, Math.min(left, window.innerWidth - tooltipW - 12));

                tooltip.style.top = `${top}px`;
                tooltip.style.left = `${left}px`;

                // Add a subtle highlight pulse to the target
                targetEl.style.position = targetEl.style.position || 'relative';
                targetEl.style.zIndex = '9999';
                targetEl.style.boxShadow = '0 0 0 4px rgba(108, 92, 231, 0.4), 0 0 20px rgba(108, 92, 231, 0.2)';
                targetEl.style.borderRadius = '8px';
                targetEl.style.transition = 'box-shadow 0.4s ease';
            }, 300);
        });
    } else {
        // Center tooltip on screen
        tooltip.style.top = `${(window.innerHeight - (tooltip.offsetHeight || 280)) / 2}px`;
        tooltip.style.left = `${(window.innerWidth - 360) / 2}px`;
    }

    // Remove highlight from previous target
    clearTourHighlights();
    // Re-highlight current (after a tiny delay so clear runs first)
    if (targetEl) {
        setTimeout(() => {
            targetEl.style.zIndex = '9999';
            targetEl.style.boxShadow = '0 0 0 4px rgba(108, 92, 231, 0.4), 0 0 20px rgba(108, 92, 231, 0.2)';
            targetEl.style.transition = 'box-shadow 0.4s ease';
        }, 50);
    }
}

function clearTourHighlights() {
    TOUR_STEPS.forEach(s => {
        if (s.target) {
            const el = document.getElementById(s.target);
            if (el) {
                el.style.zIndex = '';
                el.style.boxShadow = '';
            }
        }
    });
}

// ============================================================
// INITIALIZATION
// ============================================================

document.addEventListener('DOMContentLoaded', () => {
    // Event Listeners
    document.getElementById('generate-btn').addEventListener('click', handleGenerate);
    
    const stringInput = document.getElementById('string-input');
    if (stringInput) {
        stringInput.addEventListener('keydown', (e) => {
            if (e.key === 'Enter') handleGenerate();
        });
    }

    const exToggle = document.getElementById('examples-toggle');
    if (exToggle) {
        exToggle.addEventListener('click', (e) => {
            e.stopPropagation();
            document.getElementById('examples-menu').classList.toggle('open');
        });
    }

    const randomBtn = document.getElementById('random-example-btn');
    if (randomBtn) {
        randomBtn.addEventListener('click', handleRandomExample);
    }

    // Symbol buttons
    document.querySelectorAll('.sym-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            insertSymbol(btn.getAttribute('data-sym'));
        });
    });

    // Existing example items
    document.querySelectorAll('.example-item[data-example]').forEach(item => {
        if (item.id === 'random-example-btn') return;
        item.addEventListener('click', () => {
            const val = item.getAttribute('data-example');
            if (val === 'random') return; // Handled by separate listener but double check
            
            const idx = parseInt(val);
            loadExample(idx);
            handleGenerate();
        });
    });

    // Close menu on click outside
    document.addEventListener('click', () => {
        const menu = document.getElementById('examples-menu');
        if (menu) menu.classList.remove('open');
    });

    // Prevent menu close when clicking inside
    const menu = document.getElementById('examples-menu');
    if (menu) {
        menu.addEventListener('click', (e) => {
            e.stopPropagation();
        });
    }

    // Zoom controls
    document.getElementById('zoom-in').addEventListener('click', () => {
        currentZoom = Math.min(currentZoom + 0.1, 2);
        updateZoom();
    });
    document.getElementById('zoom-out').addEventListener('click', () => {
        currentZoom = Math.max(currentZoom - 0.1, 0.5);
        updateZoom();
    });
    document.getElementById('zoom-reset').addEventListener('click', () => {
        currentZoom = 1;
        updateZoom();
    });

    function updateZoom() {
        const canvas = document.getElementById('tree-canvas');
        canvas.style.transform = `translate(${panX}px, ${panY}px) scale(${currentZoom})`;
    }

    // ---- Drag and Scroll Zoom for Parse Tree ----
    let panX = 0, panY = 0;
    let isDragging = false;
    let dragStartX = 0, dragStartY = 0;

    const treeViewport = document.getElementById('tree-viewport');

    treeViewport.addEventListener('mousedown', (e) => {
        isDragging = true;
        dragStartX = e.clientX - panX;
        dragStartY = e.clientY - panY;
        treeViewport.classList.add('grabbing');
        e.preventDefault();
    });

    window.addEventListener('mousemove', (e) => {
        if (!isDragging) return;
        panX = e.clientX - dragStartX;
        panY = e.clientY - dragStartY;
        updateZoom();
    });

    window.addEventListener('mouseup', () => {
        isDragging = false;
        treeViewport.classList.remove('grabbing');
    });

    treeViewport.addEventListener('wheel', (e) => {
        e.preventDefault();
        const delta = e.deltaY > 0 ? -0.08 : 0.08;
        currentZoom = Math.min(Math.max(currentZoom + delta, 0.3), 3);
        updateZoom();
    }, { passive: false });

    // Tab switching
    document.querySelectorAll('.tab').forEach(tab => {
        tab.addEventListener('click', () => {
            switchTab(tab.dataset.tab);
        });
    });

    // Error close
    document.getElementById('error-close').addEventListener('click', hideError);

    // Initial load
    loadExample(0);

    // Initialize Tour
    document.getElementById('start-tour').addEventListener('click', startTour);
    document.getElementById('tour-next').addEventListener('click', () => {
        clearTourHighlights();
        if (tourIndex < TOUR_STEPS.length - 1) {
            tourIndex++;
            showTourStep();
        } else {
            endTour();
        }
    });
    document.getElementById('tour-prev').addEventListener('click', () => {
        clearTourHighlights();
        if (tourIndex > 0) {
            tourIndex--;
            showTourStep();
        }
    });
    document.getElementById('tour-skip').addEventListener('click', () => {
        clearTourHighlights();
        endTour();
    });
    document.getElementById('tour-backdrop').addEventListener('click', () => {
        clearTourHighlights();
        endTour();
    });

    // ---- Enter key to step through tree derivation ----
    document.addEventListener('keydown', (e) => {
        // Don't interfere with input fields or tour
        const tag = e.target.tagName;
        if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
        if (tourActive) return;

        if (e.key === 'Enter') {
            e.preventDefault();
            const derivation = leftmostResult || rightmostResult;
            if (!derivation || !currentGrammarInfo) return;

            // Advance step, wrap around to 0 after last step
            currentStepIndex++;
            if (currentStepIndex > derivation.length) {
                currentStepIndex = 0;
            }

            // Reveal tree up to this step (no re-render!)
            revealTreeStep(currentStepIndex);

            // Highlight the matching step in the derivation list
            document.querySelectorAll('.derivation-step').forEach(s => s.classList.remove('active'));
            const allSteps = document.querySelectorAll('.step-list .derivation-step');
            if (allSteps[currentStepIndex]) {
                allSteps[currentStepIndex].classList.add('active');
                allSteps[currentStepIndex].scrollIntoView({ behavior: 'smooth', block: 'nearest' });
            }

            // Stay on / switch to parse tree tab
            switchTab('parse-tree');
        }
    });
});
