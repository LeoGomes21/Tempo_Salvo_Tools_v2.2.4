# -*- coding: utf-8 -*-

"""
Verificação centralizada de dependências externas do plugin Tempo Salvo Tools.

Atenção:
- "import_name" é o nome usado no import Python.
- "pip_name" é o nome usado no comando pip install.
"""
import importlib.util


REQUIRED_MODULES = [
    {
        "import_name": "defusedxml",
        "pip_name": "defusedxml",
        "friendly_name": "defusedxml"
    },
    {
        "import_name": "xlsxwriter",
        "pip_name": "XlsxWriter",
        "friendly_name": "XlsxWriter"
    },
    {
        "import_name": "pyqtgraph",
        "pip_name": "pyqtgraph",
        "friendly_name": "pyqtgraph"
    },
    {
        "import_name": "simplekml",
        "pip_name": "simplekml",
        "friendly_name": "simplekml"
    },
    {
        "import_name": "OpenGL",
        "pip_name": "PyOpenGL",
        "friendly_name": "PyOpenGL"
    },
    {
        "import_name": "requests",
        "pip_name": "requests",
        "friendly_name": "requests"
    },
    {
        "import_name": "openpyxl",
        "pip_name": "openpyxl",
        "friendly_name": "openpyxl"
    },
    {
        "import_name": "PIL",
        "pip_name": "Pillow",
        "friendly_name": "Pillow"
    },
    {
        "import_name": "ezdxf",
        "pip_name": "ezdxf",
        "friendly_name": "ezdxf"
    },
    {
        "import_name": "numpy",
        "pip_name": "numpy",
        "friendly_name": "numpy"
    },
    {
        "import_name": "pandas",
        "pip_name": "pandas",
        "friendly_name": "pandas"
    },
    {
        "import_name": "scipy",
        "pip_name": "scipy",
        "friendly_name": "scipy"
    },
    {
        "import_name": "matplotlib",
        "pip_name": "matplotlib",
        "friendly_name": "matplotlib"
    },
]

def missing_required_modules():
    """
    Retorna uma lista de dicionários com os módulos ausentes.

    Exemplo:
    [
        {
            "import_name": "ezdxf",
            "pip_name": "ezdxf",
            "friendly_name": "ezdxf"
        }
    ]
    """
    missing = []

    seen = set()

    for mod in REQUIRED_MODULES:
        import_name = mod["import_name"]

        # Evita checagem duplicada, caso a lista tenha repetidos.
        if import_name in seen:
            continue

        seen.add(import_name)

        if importlib.util.find_spec(import_name) is None:
            missing.append(mod)

    return missing

def missing_pip_names():
    """Retorna apenas os nomes para usar no pip install."""
    missing = missing_required_modules()
    return [m["pip_name"] for m in missing]

def missing_friendly_names():
    """Retorna nomes amigáveis para exibir ao usuário."""
    missing = missing_required_modules()
    return [m["friendly_name"] for m in missing]