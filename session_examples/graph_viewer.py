# Generated using ai

import os
import http.server
import socketserver
import webbrowser
import json
import hashlib
from urllib.parse import parse_qs, urlparse

# Configuration
PORT = 3000

def get_file_hash(filepath):
    """Returns modification time as a simple hash/version indicator."""
    try:
        return os.path.getmtime(filepath)
    except OSError:
        return 0

def get_directory_state(directory):
    """Scans directory and returns a state object representing files and their versions."""
    dot_files = {}
    
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.dot'):
                full_path = os.path.join(root, file)
                rel_path = os.path.relpath(full_path, directory)
                dot_files[rel_path] = get_file_hash(full_path)
    
    file_list_str = json.dumps(sorted(dot_files.keys()))
    list_hash = hashlib.md5(file_list_str.encode('utf-8')).hexdigest()
    
    return {
        "list_hash": list_hash,
        "files": dot_files
    }

class ThreadingSimpleServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    pass

class GraphHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, base_dir=None, **kwargs):
        self.base_dir = base_dir
        super().__init__(*args, **kwargs)
    
    def log_message(self, format, *args):
        pass # Silence logs

    def do_GET(self):
        parsed = urlparse(self.path)
        
        if parsed.path == '/':
            self.send_response(200)
            self.send_header('Content-type', 'text/html')
            self.end_headers()
            self.wfile.write(HTML_TEMPLATE.encode())
        
        elif parsed.path == '/api/state':
            state = get_directory_state(self.base_dir)
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps(state).encode())
        
        elif parsed.path == '/api/dot':
            query = parse_qs(parsed.query)
            filename = query.get('file', [''])[0]
            
            if filename:
                filepath = os.path.join(self.base_dir, filename)
                if os.path.commonprefix([os.path.abspath(filepath), os.path.abspath(self.base_dir)]) == os.path.abspath(self.base_dir) and os.path.exists(filepath):
                    try:
                        with open(filepath, 'r', encoding='utf-8') as f:
                            content = f.read()
                        self.send_response(200)
                        self.send_header('Content-type', 'text/plain')
                        self.end_headers()
                        self.wfile.write(content.encode())
                    except Exception as e:
                        self.send_error(500, f"Error: {str(e)}")
                else:
                    self.send_error(404, "File not found")
            else:
                self.send_error(400, "No file specified")
        else:
            self.send_error(404)

HTML_TEMPLATE = """
<!DOCTYPE html>
<html>
<head>
    <title>Live Graph Viewer</title>
    <meta charset="utf-8">
    <style>
        :root {
            --bg-color: #1e1e1e;
            --sidebar-bg: #252526;
            --header-bg: #333333;
            --text-color: #cccccc;
            --accent-color: #0e639c;
            --success-color: #4cd137; /* Green for Accepting States */
        }
        body { margin: 0; padding: 0; font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; height: 100vh; display: flex; background-color: var(--bg-color); color: var(--text-color); overflow: hidden; }
        
        #sidebar { width: 250px; background-color: var(--sidebar-bg); border-right: 1px solid #454545; display: flex; flex-direction: column; flex-shrink: 0; }
        #main { flex-grow: 1; display: flex; flex-direction: column; position: relative; }
        
        .sidebar-header { padding: 15px; font-weight: bold; border-bottom: 1px solid #454545; text-transform: uppercase; font-size: 0.8rem; letter-spacing: 1px; }
        #file-list { flex-grow: 1; overflow-y: auto; list-style: none; padding: 0; margin: 0; }
        .file-item { padding: 8px 15px; cursor: pointer; display: flex; align-items: center; font-size: 0.9rem; border-bottom: 1px solid #303030; }
        .file-item:hover { background-color: #2a2d2e; }
        .file-item.active { background-color: var(--accent-color); color: white; }
        
        #toolbar { height: 50px; background-color: var(--header-bg); border-bottom: 1px solid #454545; display: flex; align-items: center; padding: 0 15px; gap: 10px; }
        
        input[type="text"] { background: #3c3c3c; border: 1px solid #555; color: white; padding: 6px 10px; border-radius: 4px; outline: none; width: 200px; }
        button { background: #444; border: none; color: white; padding: 6px 12px; border-radius: 4px; cursor: pointer; transition: background 0.2s; }
        button:hover { background: #555; }
        button:disabled { opacity: 0.5; cursor: default; }

        #graph-container { flex-grow: 1; background-color: var(--bg-color); overflow: hidden; position: relative; }
        #graph { width: 100%; height: 100%; }
        #status-bar { height: 25px; background-color: var(--accent-color); font-size: 0.8rem; display: flex; align-items: center; padding: 0 15px; color: white; }
        .search-badge { background: #d63031; color: white; font-size: 0.75rem; padding: 2px 6px; border-radius: 10px; margin-left: 5px; display: none; }

        /* --- Graph Styles --- */
        #graph svg { width: 100%; height: 100%; }
        .node text { fill: #ccc; font-family: sans-serif; pointer-events: none; }
        .edge path { stroke: #666; }
        .edge polygon { stroke: #666; fill: #666; }
        
        /* Normal Nodes */
        .node polygon, .node ellipse { stroke: #555; fill: #2d2d2d; stroke-width: 1px; transition: all 0.3s; }
        
        /* ACCEPTING STATES (Double Circle) - Green & Glowing */
        .node.accepting ellipse, .node.accepting polygon {
            stroke: var(--success-color) !important;
            stroke-width: 2px !important;
            fill: #1a331a !important; /* Slight green tint inside */
        }
        
        /* Search Matches */
        .node.matched polygon, .node.matched ellipse { stroke: #e17055 !important; stroke-width: 3px !important; fill: #4a2b2b !important; }
        .node.matched text { fill: #fff; font-weight: bold; }
        
        /* Selected (Current Search Focus) */
        .node.selected polygon, .node.selected ellipse { stroke: #00cec9 !important; stroke-width: 3px !important; fill: #1e3a3a !important; filter: drop-shadow(0 0 8px #00cec9); }
    </style>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/d3/7.8.5/d3.min.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/d3-graphviz/5.0.2/d3-graphviz.min.js"></script>
</head>
<body>
    <div id="sidebar">
        <div class="sidebar-header">Dot Files</div>
        <ul id="file-list"></ul>
    </div>
    <div id="main">
        <div id="toolbar">
            <input type="text" id="search-input" placeholder="Search nodes...">
            <span id="match-count" class="search-badge">0/0</span>
            <button id="btn-prev" disabled>↑</button>
            <button id="btn-next" disabled>↓</button>
            <div style="flex-grow: 1"></div>
            <button id="btn-reset">Reset Zoom</button>
        </div>
        <div id="graph-container"><div id="graph"></div></div>
        <div id="status-bar">Waiting for files...</div>
    </div>
    <script>
        const state = { currentFile: null, fileVersion: 0, knownFiles: {}, listHash: "", searchResults: [], currentSearchIndex: -1, graphviz: null };
        const els = { fileList: document.getElementById('file-list'), graph: document.getElementById('graph'), status: document.getElementById('status-bar'), searchInput: document.getElementById('search-input'), matchCount: document.getElementById('match-count'), btnPrev: document.getElementById('btn-prev'), btnNext: document.getElementById('btn-next'), btnReset: document.getElementById('btn-reset') };

        function initGraphviz() {
            state.graphviz = d3.select("#graph").graphviz().zoom(true).fit(true).transition(() => d3.transition().duration(500));
        }

        async function pollServer() {
            try {
                const response = await fetch('/api/state');
                const data = await response.json();
                if (data.listHash !== state.listHash) {
                    state.listHash = data.listHash; state.knownFiles = data.files; renderFileList();
                } else { state.knownFiles = data.files; }
                
                if (state.currentFile && state.knownFiles[state.currentFile] && state.knownFiles[state.currentFile] !== state.fileVersion) {
                    console.log("File changed"); loadFile(state.currentFile, true);
                }
                els.status.style.backgroundColor = "#0e639c";
            } catch (e) { els.status.style.backgroundColor = "#c0392b"; }
        }

        function renderFileList() {
            els.fileList.innerHTML = '';
            Object.keys(state.knownFiles).sort().forEach(file => {
                const li = document.createElement('li'); li.className = 'file-item';
                if (file === state.currentFile) li.classList.add('active');
                li.innerHTML = `<span style="margin-right:8px;opacity:0.7">📄</span> ${file}`;
                li.onclick = () => loadFile(file);
                els.fileList.appendChild(li);
            });
        }

        async function loadFile(filename, keepZoom = false) {
            if (!filename) return;
            els.status.innerText = `Loading ${filename}...`;
            try {
                const response = await fetch(`/api/dot?file=${encodeURIComponent(filename)}`);
                const dotContent = await response.text();
                state.currentFile = filename; state.fileVersion = state.knownFiles[filename];
                document.querySelectorAll('.file-item').forEach(el => el.classList.toggle('active', el.innerText.includes(filename)));

                state.graphviz.renderDot(dotContent).on("end", () => {
                    els.status.innerText = `Viewing: ${filename}`;
                    detectAcceptingStates(); // <--- THIS FIXES THE ISSUE
                    if (els.searchInput.value) performSearch();
                });
            } catch (e) { els.status.innerText = `Error: ${e.message}`; }
        }

        // --- THE FIX: Detect Double Circles ---
        function detectAcceptingStates() {
            d3.selectAll('.node').each(function() {
                const node = d3.select(this);
                // In Graphviz SVG, 'doublecircle' renders as 2 distinct ellipses in the same node group
                const ellipses = node.selectAll('ellipse');
                const polygons = node.selectAll('polygon');
                
                // Check if we have multiple shapes (geometry of a double border)
                if (ellipses.size() >= 2 || polygons.size() >= 2) {
                    node.classed('accepting', true);
                }
            });
        }

        function performSearch() {
            const query = els.searchInput.value.toLowerCase();
            state.searchResults = []; state.currentSearchIndex = -1;
            d3.selectAll('.node').classed('matched', false).classed('selected', false);
            if (!query) { updateSearchUI(); return; }
            d3.selectAll('.node').each(function() {
                const node = d3.select(this);
                if (node.select('title').text().toLowerCase().includes(query) || node.select('text').text().toLowerCase().includes(query)) {
                    state.searchResults.push(this); d3.select(this).classed('matched', true);
                }
            });
            if (state.searchResults.length > 0) selectResult(0);
            else updateSearchUI();
        }

        function selectResult(index) {
            if (index < 0 || index >= state.searchResults.length) return;
            state.currentSearchIndex = index;
            d3.selectAll('.node.selected').classed('selected', false);
            const selectedNode = d3.select(state.searchResults[index]);
            selectedNode.classed('selected', true);
            const bbox = state.searchResults[index].getBBox();
            const graphDiv = document.getElementById('graph');
            const scale = 1.5;
            const x = -(bbox.x + bbox.width/2) * scale + graphDiv.clientWidth/2;
            const y = -(bbox.y + bbox.height/2) * scale + graphDiv.clientHeight/2;
            d3.select("#graph").select("svg").transition().duration(750).call(state.graphviz._zoomBehavior.transform, d3.zoomIdentity.translate(x, y).scale(scale));
            updateSearchUI();
        }

        function updateSearchUI() {
            const count = state.searchResults.length;
            els.matchCount.style.display = count > 0 ? 'inline-block' : 'none';
            els.matchCount.innerText = count > 0 ? `${state.currentSearchIndex + 1}/${count}` : '';
            els.btnPrev.disabled = count === 0; els.btnNext.disabled = count === 0;
        }

        els.searchInput.addEventListener('input', performSearch);
        els.searchInput.addEventListener('keydown', (e) => { if (e.key === 'Enter' && state.searchResults.length) selectResult(e.shiftKey ? (state.currentSearchIndex - 1 + state.searchResults.length) % state.searchResults.length : (state.currentSearchIndex + 1) % state.searchResults.length); });
        els.btnNext.addEventListener('click', () => selectResult((state.currentSearchIndex + 1) % state.searchResults.length));
        els.btnPrev.addEventListener('click', () => selectResult((state.currentSearchIndex - 1 + state.searchResults.length) % state.searchResults.length));
        els.btnReset.addEventListener('click', () => state.graphviz.resetZoom(d3.transition().duration(750)));

        initGraphviz(); pollServer(); setInterval(pollServer, 1000);
    </script>
</body>
</html>
"""

def main():
    directory = os.path.dirname(os.path.abspath(__file__))
    handler = lambda *args, **kwargs: GraphHandler(*args, base_dir=directory, **kwargs)
    with ThreadingSimpleServer(("", PORT), handler) as httpd:
        url = f"http://localhost:{PORT}"
        print(f"🚀 Graph Viewer running at {url}")
        print(f"📁 Watching: {directory}")
        webbrowser.open(url)
        try: httpd.serve_forever()
        except KeyboardInterrupt: print("\n👋 Stopped")

if __name__ == "__main__":
    main()