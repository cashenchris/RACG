racg — Computational Toolkit for 2-dimensional right-angled Coxeter groups

racg is a Python module providing graph–theoretic tools for studying 2-dimensional right-angled Coxeter groups (RACGs).
All functions operate on networkx.Graph() objects and extract geometric, combinatorial, and quasi-isometric properties directly from the presentaiton graph.

The module includes tools for:

CFS (Component of Full Support/Constructed From Squares) and strong CFS detection

Stable cycles & compliant cycles

Square-complete subgraphs

Dani–Levcovitz detection

JSJ & splitting structure

Nguyen–Tran RAAG criteria

Cylinder graphs and ZZ–RACG obstructions

Satellite dismantling

Export to TikZ and optional visualization


🔧 Installation

From GitHub:
```bash
pip install git+https://github.com/cashenchris/RACG.git
```

or clone locally:
```bash
git clone https://github.com/cashenchris/RACG.git
cd RACG
pip install .
```

📦 Dependencies

Core functionality requires only:

networkx >= 3.2.1  
numpy  


Visualization tools are optional.
If you wish to draw graphs interactively, uncomment the relevant imports
in racg.py and install:

```bash
pip install matplotlib netgraph
```


Many functions include doctests. Run all tests via:

```bash
python racg.py
```

🔁 Relation to RACG Enumeration Dataset

This repository supports computations used in the dataset:

Triangle-free CFS graphs (≤12 vertices) and associated RACG data, available at: http://dx.doi.org/10.5281/zenodo.17752422

That dataset includes:

full enumeration of triangle-free CFS graphs up to 12 vertices, contained in a  pandas DataFrame including associated data about the RACG defined by the graph. 

lookup tools 


📄 License — The Unlicense

This repository is released into the public domain.
See the LICENSE file for full text.

This is free and unencumbered software released into the public domain.

📬 Contact

Christopher H. Cashen
TU Wien
Institute of Discrete Mathematics and Geometry
📧 christopher.cashen@tuwien.ac.at
