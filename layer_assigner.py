# -*- coding: utf-8 -*-

"""
Script para automação de tarefas em desenhos DXF. Oferece dois modos de operação:
1. Análise por Área: Agrupa peças com geometria idêntica (área e perímetro).
2. Análise por Texto: Identifica peças com base em textos próximos (ex: "CHAPA XXX") e as agrupa.

Ambos os modos também executam tarefas de organização de layers padrão.

Persona: Desenvolvedor Python Sênior
Projeto: Ferramenta de automação para desenhos de estruturas metálicas.
Revisão: 20.0 - 2025-10-07 (Implementado método alternativo de análise por texto)
"""

import ezdxf
import os
import math
import re
import unicodedata
from collections import defaultdict
import tkinter as tk
from tkinter import ttk, filedialog, scrolledtext
import sys
import threading
import queue
from ezdxf.path import make_path
from ezdxf.math import area as path_area, Vec3, BoundingBox
from ezdxf import DXFValueError

# --- CONFIGURAÇÕES ---
# 1 = Vermelho, 2 = Amarelo, 3 = Verde, 4 = Ciano, 5 = Azul, 6 = Magenta, 7 = Branco/Preto
COLOR_RED = 1
COLOR_YELLOW = 2
COLOR_GREEN = 3

# --- CONFIGURAÇÕES PARA ANÁLISE POR TEXTO (MÉTODO 2) ---
RAIO_DE_BUSCA = 800.0  # Ajuste conforme a escala desenho.
ARROW_MAX_SIZE = 4.0   # Tamanho máximo (unidades do desenho) para reconhecer uma entidade pequena como seta
ARROW_MAX_SIZE_ALT = 12.0  # Segundo limite maior usado com heurística de proporção
ARROW_ASPECT_RATIO = 4.0   # Proporção (maior/menor) mínima para considerar entidade longa e fina (seta)
ARROW_PROXIMITY = 20.0    # Distância máxima para considerar uma entidade próxima a uma dimensão (unidades do desenho)

# --- PALETA DE CORES E CAMADAS PADRÃO (MÉTODO 2) ---
CHAPA_COLORS = [6, 4, 3, 5, 230, 150] # Magenta, Ciano, Verde, Azul, Laranja, Roxo...

SEMANTIC_LAYERS = {
    "chumbador": ("CHUMBADORES", 1), # Vermelho
    "perfil":    ("PERFIS", 1),      # Vermelho
    "eixo":      ("EIXOS", 2),        # Amarelo
}

COLOR_FURO = 1       # Vermelho
COLOR_LAYER_0 = 2    # Amarelo
COLOR_TEXTO_ALVO = 3 # Verde

PADROES_ALVO = [
    re.compile(r'CHAPA\s+"?([A-Z0-9]+)"?', re.IGNORECASE),
    re.compile(r'CH-([A-Z0-9]+)', re.IGNORECASE)
]

# Mapa para organizar layers existentes em NOVOS layers
LAYER_ORGANIZATION_MAP = {
    # 'NOME_ANTIGO': ('NOME_NOVO', CODIGO_COR),
    'EIXO': ('ORGANIZADO_EIXO', COLOR_YELLOW),
    'G-SIMBOLO': ('ORGANIZADO_G-SIMBOLO', COLOR_YELLOW),
    'PERFIL': ('ORGANIZADO_PERFIL', COLOR_RED),
    'CHU-CHUMBADOR': ('ORGANIZADO_CHU-CHUMBADOR', COLOR_RED),
}

# Mapa para subclassificar entidades do layer '0' em NOVOS layers
LAYER_ZERO_SUBCLASSIFICATION = {
    # (TIPOS_DE_ENTIDADE): ('NOME_NOVO_LAYER', CODIGO_COR),
    ('TEXT', 'MTEXT'): ('LAYER0_TEXTOS', COLOR_GREEN),
    ('HATCH',): ('LAYER0_HACHURAS', COLOR_RED),
}

# --- CONFIGURAÇÕES PARA ANÁLISE POR ÁREA (MÉTODO 1) ---
PECA_EQ_LAYER_COLORS = [1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15] # Amarelo (2) removido
PECA_EQ_LAYER_PREFIX = "PECA_EQ"

# --- FUNÇÕES AUXILIARES GERAIS ---

def get_aci_color_name(aci_index):
    color_map = {1: "Vermelho", 2: "Amarelo", 3: "Verde", 4: "Ciano", 5: "Azul", 6: "Magenta"}
    return color_map.get(aci_index, f"ACI {aci_index}")

def organize_existing_layers(doc, msp):
    """
    Cria uma nova estrutura de layers e move as entidades dos layers antigos para os novos.
    """
    print("\n--- Reorganizando layers existentes para nova estrutura ---")
    map_upper = {k.upper(): v for k, v in LAYER_ORGANIZATION_MAP.items()}
    moved_count = 0

    for old_layer_name_upper, (new_layer_name, new_color) in map_upper.items():
        # Cria o novo layer se ele não existir
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': new_color})
        
        # Encontra todas as entidades no layer antigo (insensível a maiúsculas/minúsculas)
        entities_to_move = msp.query(f'*[layer=="{old_layer_name_upper}"]')
        
        count = 0
        for entity in entities_to_move:
            entity.dxf.layer = new_layer_name
            count += 1
        
        if count > 0:
            print(f" - {count} entidades movidas do layer '{old_layer_name_upper}' para '{new_layer_name}'.")
            moved_count += count

    if moved_count == 0:
        print("Nenhuma entidade encontrada nos layers de origem para reorganizar.")

def subclassify_layer_zero(doc, msp):
    """
    Move entidades específicas do layer '0' para novos layers subclassificados.
    """
    print("\n--- Subclassificando entidades do Layer '0' em novos layers ---")
    moved_count = 0
    
    # Primeiro, cria todos os layers necessários
    for _, (new_layer_name, new_color) in LAYER_ZERO_SUBCLASSIFICATION.items():
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': new_color})

    # Busca todas as entidades no layer '0'
    entities_on_layer_zero = msp.query("*[layer=='0']")
    
    for entity in entities_on_layer_zero:
        dxftype = entity.dxftype()
        # Itera sobre as regras de subclassificação
        for entity_types, (new_layer_name, _) in LAYER_ZERO_SUBCLASSIFICATION.items():
            if dxftype in entity_types:
                entity.dxf.layer = new_layer_name
                moved_count += 1
                break # Pára de verificar outras regras para esta entidade

    if moved_count > 0:
        print(f" - {moved_count} entidades do layer '0' foram movidas para layers subclassificados.")
    else:
        print("Nenhuma entidade correspondente às regras de subclassificação foi encontrada no layer '0'.")

def organize_remaining_layer_zero_entities(doc, msp):
    """
    Move todas as entidades restantes no layer '0' para um novo layer 'Linhas de chamadas'.
    Esta função deve ser executada após a subclassificação.
    """
    print("\n--- Organizando entidades restantes no Layer '0' ---")
    new_layer_name = "Linhas de chamadas"
    moved_count = 0
    
    # Busca todas as entidades que AINDA estão no layer '0'
    remaining_entities = msp.query("*[layer=='0']")
    
    if remaining_entities:
        # Cria o novo layer se ele não existir
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': COLOR_YELLOW})

        for entity in remaining_entities:
            # Move a entidade para o novo layer
            entity.dxf.layer = new_layer_name
            moved_count += 1
        
    if moved_count > 0:
        print(f" - {moved_count} entidades restantes do layer '0' foram movidas para o layer '{new_layer_name}'.")
    else:
        print("Nenhuma entidade restou no layer '0' para ser organizada.")

# --- FUNÇÕES PARA ANÁLISE POR ÁREA (MÉTODO 1) ---

def process_drawing_by_area(filepath: str, precision: int):
    """
    Executa as rotinas de otimização no desenho: reorganiza, subclassifica e agrupa peças por área/perímetro.
    """
    doc, msp = _load_drawing(filepath)
    if not doc:
        return

    _run_common_organization_tasks(doc, msp)

    _analyze_and_group_by_area(doc, msp, precision, filepath)

def get_closed_entity_properties(entity) -> tuple[str, float, float] | None:
    """
    Verifica se uma entidade é uma forma fechada e calcula sua área e perímetro.
    """
    dxftype = entity.dxftype()
    is_a_closed_shape = (dxftype == 'CIRCLE') or (hasattr(entity, 'is_closed') and entity.is_closed)

    if not is_a_closed_shape:
        return None

    try:
        if dxftype == 'CIRCLE':
            radius = entity.dxf.radius
            area = math.pi * radius**2
            perimeter = 2 * math.pi * radius
            return dxftype, abs(area), perimeter
        else:
            path = make_path(entity)
            vertices = list(path.flattening(distance=0.01))
            area = path_area(vertices)
            perimeter = 0.0
            if len(vertices) > 1:
                vec3_vertices = [Vec3(v) for v in vertices]
                for i in range(len(vec3_vertices) - 1):
                    perimeter += vec3_vertices[i].distance(vec3_vertices[i+1])
            if area > 1e-9:
                return dxftype, abs(area), perimeter
    except (DXFValueError, AttributeError, IndexError, RuntimeError, TypeError):
        return None
    return None

def _run_common_organization_tasks(doc, msp):
    organize_existing_layers(doc, msp)
    subclassify_layer_zero(doc, msp)
    organize_remaining_layer_zero_entities(doc, msp)

def _analyze_and_group_by_area(doc, msp, precision, filepath: str):
    """Agrupa peças equivalentes com base na área e perímetro."""
    print("\n--- Analisando geometrias para encontrar peças equivalentes ---")
    entities_by_properties = defaultdict(list)
    print(f"Analisando todas as {len(msp)} entidades do desenho com precisão de {precision} casas decimais...")

    for entity in msp:
        if not hasattr(entity, 'dxftype'):
            continue
        properties = get_closed_entity_properties(entity)
        if properties:
            dxftype, area, perimeter = properties
            prop_key = (dxftype, round(area, precision), round(perimeter, precision))
            entities_by_properties[prop_key].append(entity)

    if not entities_by_properties:
        print("Nenhuma forma fechada válida foi encontrada para agrupar.")
    else:
        print(f"\nForam encontrados {len(entities_by_properties)} grupos distintos de peças com geometrias equivalentes.")
        layer_counter = 0
        for prop_key, entities in sorted(entities_by_properties.items()):
            layer_counter += 1
            new_layer_name = f"{PECA_EQ_LAYER_PREFIX}_{layer_counter}"
            
            entity_type, area_key, perimeter_key = prop_key
            is_like_a_circle = False
            # Verifica se a forma é um círculo ou se aproxima de um
            if entity_type == 'CIRCLE':
                is_like_a_circle = True
            elif perimeter_key > 1e-6: # Evita divisão por zero
                isoperimetric_ratio = (4 * math.pi * area_key) / (perimeter_key**2)
                if isoperimetric_ratio > 0.98: # Se a forma for muito próxima de um círculo
                    is_like_a_circle = True

            if is_like_a_circle:
                color_index = COLOR_RED
            else:
                color_index = PECA_EQ_LAYER_COLORS[(layer_counter - 1) % len(PECA_EQ_LAYER_COLORS)]
            print(f" - Grupo {layer_counter}: Criando layer '{new_layer_name}' para {len(entities)} peças do tipo '{entity_type}' com área ~{area_key} e perímetro ~{perimeter_key}. Cor: {'Vermelho' if is_like_a_circle else 'Padrão'}")

            if new_layer_name not in doc.layers:
                doc.layers.new(name=new_layer_name, dxfattribs={'color': color_index})
            for entity in entities:
                entity.dxf.layer = new_layer_name

    _save_drawing(doc, filepath)

# --- FUNÇÕES PARA ANÁLISE POR TEXTO (MÉTODO 2) ---

def obter_centro_geometrico(entity):
    try:
        bbox = BoundingBox(entity.vertices_in_wcs())
        return bbox.center.xy
    except (AttributeError, TypeError, ValueError):
        try:
            if entity.dxftype() in ['CIRCLE', 'ARC']:
                return entity.dxf.center.xy
            if entity.dxftype() in ['TEXT', 'MTEXT', 'INSERT', 'ATTRIB']:
                return entity.dxf.insert.xy
        except AttributeError:
            return None
    return None

def get_entity_bbox_size(entity):
    """Retorna (width, height) do bounding box da entidade em WCS, ou (None, None) se inválido."""
    dx = None
    try:
        dx = entity.dxftype()
    except Exception:
        dx = None

    # LINE: usar start/end se disponível
    if dx == 'LINE':
        try:
            s = entity.dxf.start
            e = entity.dxf.end
            xs = [s[0], e[0]]
            ys = [s[1], e[1]]
            width = max(xs) - min(xs)
            height = max(ys) - min(ys)
            return (abs(width), abs(height))
        except Exception:
            pass

    # TRACE: tenta obter pontos através de vários métodos
    if dx == 'TRACE' or dx == 'POLYLINE' or dx == 'LWPOLYLINE':
        # 1) vertices_in_wcs
        try:
            verts = entity.vertices_in_wcs()
            xs = [v[0] for v in verts]
            ys = [v[1] for v in verts]
            if xs and ys:
                width = max(xs) - min(xs)
                height = max(ys) - min(ys)
                return (abs(width), abs(height))
        except Exception:
            pass
        # 2) points() method
        try:
            pts = list(entity.points())
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            if xs and ys:
                width = max(xs) - min(xs)
                height = max(ys) - min(ys)
                return (abs(width), abs(height))
        except Exception:
            pass

    # Fallback geral: vertices_in_wcs for other entity types
    try:
        verts = entity.vertices_in_wcs()
        xs = [v[0] for v in verts]
        ys = [v[1] for v in verts]
        if not xs or not ys:
            return (None, None)
        width = max(xs) - min(xs)
        height = max(ys) - min(ys)
        return (abs(width), abs(height))
    except Exception:
        pass

    # CIRCLE/ARC fallback
    try:
        if dx in ['CIRCLE', 'ARC']:
            r = float(entity.dxf.radius)
            return (2*r, 2*r)
    except Exception:
        pass

    return (None, None)

def is_arrow(entity):
    """Heurística simples para detectar setas/arrowheads: geometria curta/pequena."""
    try:
        dx = entity.dxftype()
    except Exception:
        return False
    if dx not in ('LINE', 'TRACE', 'LWPOLYLINE', 'POLYLINE'):
        return False
    w, h = get_entity_bbox_size(entity)
    if w is None or h is None:
        return False
    maxdim = max(w, h)
    mindim = min(w, h) if min(w, h) > 0 else 0.0
    if maxdim <= ARROW_MAX_SIZE:
        return True
    if maxdim <= ARROW_MAX_SIZE_ALT and mindim > 0:
        aspect = maxdim / mindim
        if aspect >= ARROW_ASPECT_RATIO:
            return True
    return False

def ensure_layer(doc, layer_name, color):
    if layer_name not in doc.layers:
        print(f"  + Criando camada '{layer_name}' com a cor {get_aci_color_name(color)}.")
        doc.layers.new(name=layer_name, dxfattribs={'color': color})
    else:
        doc.layers.get(layer_name).dxf.color = color

def set_layer0_to_yellow(doc):
    """Define a cor da camada '0' para amarelo."""
    layer_name = '0'
    try:
        if layer_name not in doc.layers:
            print(f"  + Criando camada '{layer_name}' com a cor {get_aci_color_name(COLOR_LAYER_0)}.")
            doc.layers.new(name=layer_name, dxfattribs={'color': COLOR_LAYER_0})
        else:
            doc.layers.get(layer_name).dxf.color = COLOR_LAYER_0
            print(f"  * Camada '{layer_name}' atualizada para cor {get_aci_color_name(COLOR_LAYER_0)}.")
    except Exception as e:
        print(f"Aviso: não foi possível ajustar a cor da camada '0': {e}")

def _normalize_layer_name(name: str) -> str:
    """Normaliza o nome de uma camada para correspondência."""
    if not name:
        return ''
    nfkd = unicodedata.normalize('NFKD', name)
    only_ascii = ''.join([c for c in nfkd if not unicodedata.combining(c)])
    cleaned = only_ascii.replace(' ', '').replace('-', '').replace('_', '').lower()
    return cleaned

def set_g_symbol_to_yellow(doc):
    """Garante que qualquer camada tipo G-SYMBOL seja definida como amarela."""
    candidates = ['G-SYMBOL', 'G SIMBOLO', 'G_SIMBOLO', 'GSYMBOL']
    normalized_candidates = {_normalize_layer_name(c): c for c in candidates}
    found = False
    try:
        for layer in doc.layers:
            nl = _normalize_layer_name(layer.dxf.name)
            if nl in normalized_candidates:
                layer.dxf.color = COLOR_LAYER_0
                print(f"  * Camada existente '{layer.dxf.name}' atualizada para cor {get_aci_color_name(COLOR_LAYER_0)}.")
                found = True
        if not found:
            default_name = 'G SIMBOLO'
            ensure_layer(doc, default_name, COLOR_LAYER_0)
    except Exception as e:
        print(f"Aviso: erro ao procurar camadas G-SYMBOL: {e}")

def process_cotas_and_texts(doc, msp, processed_handles):
    """Move DIMENSION para 'COTAS' e MTEXT para 'TEXTO'."""
    cotas_layer = 'COTAS'
    texto_layer = 'TEXTO'
    ensure_layer(doc, cotas_layer, COLOR_LAYER_0)
    ensure_layer(doc, texto_layer, COLOR_TEXTO_ALVO)

    for ent in msp:
        if ent.dxf.handle in processed_handles:
            continue
        dxftype = ent.dxftype()
        if dxftype == 'DIMENSION':
            ent.dxf.layer = cotas_layer
            ent.dxf.color = COLOR_LAYER_0
            processed_handles.add(ent.dxf.handle)
        elif dxftype == 'MTEXT':
            ent.dxf.layer = texto_layer
            ent.dxf.color = COLOR_TEXTO_ALVO
            processed_handles.add(ent.dxf.handle)

def collect_dimension_centers(msp):
    """Escaneia o modelspace em busca de entidades DIMENSION e retorna seus centros."""
    centers = []
    for ent in msp.query('DIMENSION'):
        c = obter_centro_geometrico(ent)
        if c:
            centers.append(c)
    return centers

def move_nearby_unclosed_lines_to_setas(doc, msp, alvos_chapa, processed_handles, arrow_proximity, raio_de_busca):
    """Move linhas/traces não fechadas próximas às CHAPAs para a camada 'SETAS'."""
    setas_layer = 'SETAS'
    ensure_layer(doc, setas_layer, COLOR_LAYER_0)
    
    chapa_centers = [loc for locs in alvos_chapa.values() for loc in locs if loc]

    for entity in msp:
        if entity.dxf.handle in processed_handles:
            continue
        
        dxftype = entity.dxftype()
        if dxftype not in ('LINE', 'TRACE', 'LWPOLYLINE', 'POLYLINE'):
            continue
        
        if getattr(entity, 'is_closed', False):
            continue

        centro = obter_centro_geometrico(entity)
        if not centro:
            continue

        for chapa_loc in chapa_centers:
            if math.dist(centro, chapa_loc) <= raio_de_busca:
                entity.dxf.layer = setas_layer
                entity.dxf.color = COLOR_LAYER_0
                processed_handles.add(entity.dxf.handle)
                break

def process_drawing_by_text(filepath: str, **kwargs):
    """
    Executa a reestruturação do desenho com base na identificação de textos.
    """
    doc, msp = _load_drawing(filepath)
    if not doc:
        return

    print("Iniciando reestruturação com base em texto (Método 2).")
    set_layer0_to_yellow(doc)
    set_g_symbol_to_yellow(doc)
    
    processed_handles = set()
    
    # --- FASE 1: SEMÂNTICA ---
    print("\n--- Fase 1: Identificando sistemas (Perfis, Chumbadores, Eixos) ---")
    for keyword, (layer_name, color) in SEMANTIC_LAYERS.items():
        ensure_layer(doc, layer_name, color)

    for entity in msp:
        original_layer = entity.dxf.layer.lower()
        eh_tracejado = hasattr(entity.dxf, 'linetype') and entity.dxf.linetype.lower() not in ['continuous', 'byblock', 'bylayer']

        for keyword, (target_layer, _) in SEMANTIC_LAYERS.items():
            if (keyword == 'eixo' and eh_tracejado) or keyword in original_layer:
                entity.dxf.layer = target_layer
                entity.dxf.color = 256 # BYLAYER
                processed_handles.add(entity.dxf.handle)
                break

    dimension_centers = collect_dimension_centers(msp)

    # --- FASE 2: AGRUPAMENTO DAS CHAPAS ---
    print("\n--- Fase 2: Mapeando e agrupando Chapas por texto ---")
    alvos_chapa = defaultdict(list)
    for entity in msp.query('TEXT MTEXT ATTRIB'):
        text_content = ""
        if entity.dxftype() in ('TEXT', 'ATTRIB'):
            text_content = entity.dxf.text
        elif entity.dxftype() == 'MTEXT':
            text_content = entity.plain_text()
        
        for padrao in PADROES_ALVO:
            match = padrao.search(text_content)
            if match:
                nome_peca = match.group(1).upper()
                alvos_chapa[nome_peca].append(obter_centro_geometrico(entity))
                entity.dxf.color = COLOR_TEXTO_ALVO
                processed_handles.add(entity.dxf.handle)
                break

    color_index = 0
    for nome_peca, localizacoes in alvos_chapa.items():
        novo_layer_name = f"CHAPA {nome_peca}"
        cor_da_chapa = CHAPA_COLORS[color_index % len(CHAPA_COLORS)]
        ensure_layer(doc, novo_layer_name, cor_da_chapa)
        color_index += 1

        for entity in msp:
            if entity.dxf.handle in processed_handles:
                continue
            
            loc_entidade = obter_centro_geometrico(entity)
            if not loc_entidade:
                continue

            is_closed = getattr(entity, 'is_closed', False)
            original_layer = entity.dxf.layer.lower()

            if not is_closed and original_layer == '0':
                entity.dxf.color = COLOR_LAYER_0
                continue

            for loc_alvo in localizacoes:
                if loc_alvo and math.dist(loc_entidade, loc_alvo) <= RAIO_DE_BUSCA:
                    if is_arrow(entity):
                        entity.dxf.color = COLOR_LAYER_0
                        break

                    entity.dxf.layer = novo_layer_name
                    entity.dxf.color = 256 # BYLAYER
                    processed_handles.add(entity.dxf.handle)
                    break

    move_nearby_unclosed_lines_to_setas(doc, msp, alvos_chapa, processed_handles, ARROW_PROXIMITY, RAIO_DE_BUSCA)

    # --- FASE 3: COTAS, TEXTOS E LIMPEZA ---
    print("\n--- Fase 3: Processando Cotas, Textos, Furos e Limpeza ---")
    process_cotas_and_texts(doc, msp, processed_handles)

    for entity in msp:
        if entity.dxf.handle in processed_handles:
            continue

        dxftype = entity.dxftype()
        if dxftype == 'HATCH':
            ensure_layer(doc, 'HATCHES', COLOR_FURO)
            entity.dxf.layer = 'HATCHES'
            entity.dxf.color = COLOR_FURO
            processed_handles.add(entity.dxf.handle)
            continue

        is_hole_candidate = (
            dxftype == 'CIRCLE' or 
            dxftype == 'TRACE' or
            (dxftype in ['LWPOLYLINE', 'POLYLINE'] and getattr(entity, 'is_closed', False))
        )
        if is_hole_candidate:
            entity.dxf.color = COLOR_FURO
        elif entity.dxf.layer.lower() == '0':
            entity.dxf.color = COLOR_LAYER_0

    print("\n" + "="*50)
    print("Reestruturação por texto concluída!")
    _save_drawing_with_report(doc, msp, filepath, processed_handles)


# --- FUNÇÕES DE GERENCIAMENTO (CARREGAR/SALVAR/MENU) ---

def _load_drawing(filepath: str):
    """Carrega um arquivo DXF e retorna o documento e o modelspace."""
    try:
        print(f"Carregando o desenho: {os.path.basename(filepath)}...")
        doc = ezdxf.readfile(filepath)
        msp = doc.modelspace()
        return doc, msp
    except Exception as e:
        print(f"Erro ao carregar o arquivo DXF: {e}")
        return None, None

def _save_drawing(doc, original_filepath: str):
    """Salva o documento modificado com um novo nome."""
    base, ext = os.path.splitext(original_filepath)
    output_path = f"{base}_processado{ext}"

    try:
        print(f"\nSalvando o desenho modificado em: {output_path}")
        doc.saveas(output_path)
        print("\nProcesso concluído com sucesso!")
    except IOError as e:
        if isinstance(e, PermissionError) or (hasattr(e, 'errno') and e.errno == 13):
            print(f"\nERRO DE PERMISSÃO AO SALVAR O ARQUIVO: {output_path}")
            print("Por favor, feche o arquivo no seu software CAD e tente executar o script novamente.")
        else:
            print(f"Erro fatal ao tentar salvar o arquivo: {e}")

def _save_drawing_with_report(doc, msp, original_filepath: str, processed_handles: set):
    """Salva o desenho e gera relatórios de contagem e handles."""
    base, ext = os.path.splitext(original_filepath)
    output_path = f"{base}_processado_texto{ext}"

    try:
        print(f"\nSalvando o desenho modificado em: {output_path}")
        doc.saveas(output_path)
        print("\nProcesso concluído com sucesso!")
    except IOError as e:
        if isinstance(e, PermissionError) or (hasattr(e, 'errno') and e.errno == 13):
            print(f"\nERRO DE PERMISSÃO AO SALVAR O ARQUIVO: {output_path}")
            print("Por favor, feche o arquivo no seu software CAD e tente executar o script novamente.")
        else:
            print(f"Erro fatal ao tentar salvar o arquivo: {e}")
        return

    # --- RELATÓRIO: contagens por camada ---
    layer_counts = defaultdict(int)
    for ent in msp:
        layer_counts[ent.dxf.layer] += 1

    report_path = os.path.splitext(output_path)[0] + '_report.txt'
    try:
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write('Relatório de contagens por camada\n')
            f.write(f'Arquivo processado: {os.path.basename(output_path)}\n')
            f.write('---\n')
            total = 0
            for layer_name, count in sorted(layer_counts.items()):
                f.write(f"{layer_name}: {count}\n")
                total += count
            f.write('---\n')
            f.write(f'Total de entidades: {total}\n')
            f.write(f'Entidades processadas (handles): {len(processed_handles)}\n')
        print(f"Relatório de contagem por camada salvo em: '{os.path.abspath(report_path)}'")
    except Exception as e:
        print(f"Erro ao gravar relatório: {e}")

def main():
    """
    Função principal que gerencia a interface com o usuário no console.
    """
    print("---------------------------------------------------------------------")
    print("---      Ferramenta de Otimização e Análise de Layers para DXF   ---")
    print("---------------------------------------------------------------------")
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Otimizador de Layers DXF")
        self.geometry("700x600")

        self.filepath = tk.StringVar()
        self.analysis_method = tk.StringVar(value="1")
        self.precision = tk.StringVar(value="2")
        self.queue = queue.Queue()

        self.create_widgets()
        self.redirect_stdout()

    def create_widgets(self):
        main_frame = ttk.Frame(self, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # --- File Selection ---
        file_frame = ttk.LabelFrame(main_frame, text="Arquivo DXF", padding="10")
        file_frame.pack(fill=tk.X, pady=5)
        file_frame.columnconfigure(1, weight=1)

        ttk.Label(file_frame, text="Caminho:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(file_frame, textvariable=self.filepath).grid(row=0, column=1, sticky=tk.EW, padx=5, pady=5)
        ttk.Button(file_frame, text="Procurar...", command=self.browse_file).grid(row=0, column=2, padx=5, pady=5)

        # --- Analysis Method ---
        method_frame = ttk.LabelFrame(main_frame, text="Método de Análise", padding="10")
        method_frame.pack(fill=tk.X, pady=5)

        ttk.Radiobutton(method_frame, text="Análise por Área (peças com geometria idêntica)", variable=self.analysis_method, value="1", command=self.toggle_precision).pack(anchor=tk.W)
        self.precision_frame = ttk.Frame(method_frame, padding="0 0 0 20")
        self.precision_frame.pack(fill=tk.X)
        ttk.Label(self.precision_frame, text="Precisão (casas decimais):").pack(side=tk.LEFT, padx=5)
        ttk.Entry(self.precision_frame, textvariable=self.precision, width=5).pack(side=tk.LEFT)

        ttk.Radiobutton(method_frame, text="Análise por Texto (identifica 'CHAPA XXX')", variable=self.analysis_method, value="2", command=self.toggle_precision).pack(anchor=tk.W)

        # --- Process Button ---
        self.process_button = ttk.Button(main_frame, text="Processar Desenho", command=self.start_processing)
        self.process_button.pack(pady=10, fill=tk.X)

        # --- Output Console ---
        console_frame = ttk.LabelFrame(main_frame, text="Console de Saída", padding="10")
        console_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        self.console = scrolledtext.ScrolledText(console_frame, wrap=tk.WORD, height=15)
        self.console.pack(fill=tk.BOTH, expand=True)

    def toggle_precision(self):
        if self.analysis_method.get() == "1":
            self.precision_frame.pack(fill=tk.X)
        else:
            self.precision_frame.pack_forget()

    def browse_file(self):
        filename = filedialog.askopenfilename(
            title="Selecione o arquivo DXF",
            filetypes=(("Arquivos DXF", "*.dxf"), ("Todos os arquivos", "*.*"))
        )
        if filename:
            self.filepath.set(filename)

    def start_processing(self):
        filepath = self.filepath.get()
        if not filepath or not os.path.exists(filepath):
            self.console.insert(tk.END, "ERRO: Por favor, selecione um arquivo DXF válido.\n")
            return

        self.console.delete('1.0', tk.END)
        self.process_button.config(state=tk.DISABLED, text="Processando...")

        method = self.analysis_method.get()
        if method == "1":
            try:
                precision = int(self.precision.get())
                if precision < 0: raise ValueError
                target = lambda: process_drawing_by_area(filepath, precision)
            except ValueError:
                self.console.insert(tk.END, "ERRO: A precisão deve ser um número inteiro positivo.\n")
                self.processing_finished()
                return
        else: # method == "2"
            target = lambda: process_drawing_by_text(filepath)

        self.thread = threading.Thread(target=target)
        self.thread.daemon = True
        self.thread.start()
        self.after(100, self.check_queue)

    def check_queue(self):
        try:
            while True: # Loop to empty the queue
                line = self.queue.get_nowait()
                self.console.insert(tk.END, line)
                self.console.see(tk.END)
        except queue.Empty:
            pass

        if self.thread.is_alive():
            self.after(100, self.check_queue)
        else:
            self.processing_finished()

    def processing_finished(self):
        self.process_button.config(state=tk.NORMAL, text="Processar Desenho")
        self.console.insert(tk.END, "\n--- FIM DO PROCESSO ---\n")
        self.console.see(tk.END)

    def redirect_stdout(self):
        class QueueIO:
            def __init__(self, q):
                self.queue = q

            def write(self, text):
                self.queue.put(text)

            def flush(self):
                sys.__stdout__.flush()

        sys.stdout = QueueIO(self.queue)
        sys.stderr = QueueIO(self.queue)

def main():
    app = App()
    app.mainloop()

if __name__ == "__main__":
    main()
