# Developer setup (Conda)

## 1) Install Conda (if needed)
Choose one:
- Miniforge (recommended): https://github.com/conda-forge/miniforge
- Miniconda: https://docs.conda.io/en/latest/miniconda.html

## 2) Create env
```bash
conda env create -f environment.yml
conda activate satpredict
```

## 3) Verify
```bash
python -V
python -m satpredict.cli --help
```

## 4) Update env after dependency changes
```bash
conda env update -f environment.yml --prune
```

## 5) Remove env
```bash
conda env remove -n satpredict
```
