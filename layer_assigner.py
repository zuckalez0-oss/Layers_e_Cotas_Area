# -*- coding: utf-8 -*-

"""
Script para automação de tarefas em desenhos DXF. Oferece dois modos de operação:
1. Análise por Área: Agrupa peças com geometria idêntica (área e perímetro).
2. Análise por Texto: Identifica peças com base em textos próximos (ex: "CHAPA XXX") e as agrupa.

Ambos os modos também executam tarefas de organização de layers padrão.

Persona: Desenvolvedor Python Sênior
Projeto: Ferramenta de automação para desenhos de estruturas metálicas.
Revisão: 23.0 - 2025-10-08 (Corrigido para identificar vistas de furo retangulares, não apenas quadradas)
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
COLOR_MAGENTA = 6

# --- CONFIGURAÇÕES PARA ANÁLISE POR TEXTO (MÉTODO 2) ---
RAIO_DE_BUSCA = 800.0  # Ajuste conforme a escala desenho.
ARROW_MAX_SIZE = 4.0   # Tamanho máximo (unidades do desenho) para reconhecer uma entidade pequena como seta
ARROW_MAX_SIZE_ALT = 12.0  # Segundo limite maior usado com heurística de proporção
ARROW_ASPECT_RATIO = 4.0   # Proporção (maior/menor) mínima para considerar entidade longa e fina (seta)
ARROW_PROXIMITY = 20.0     # Distância máxima para considerar uma entidade próxima a uma dimensão (unidades do desenho)

# --- PALETA DE CORES E CAMADAS PADRÃO (MÉTODO 2) ---
CHAPA_COLORS = [6, 4, 3, 5, 230, 150] # Magenta, Ciano, Verde, Azul, Laranja, Roxo...

SEMANTIC_LAYERS = {
    "chumbador": ("CHUMBADORES", 1), # Vermelho
    "perfil":    ("PERFIS", 1),      # Vermelho
    "eixo":      ("EIXOS", 2),       # Amarelo
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

# ●▽●▽●▽●▽●▽●▽●▽● CONFIGURAÇÕES PARA ANÁLISE POR ÁREA (MÉTODO 1) ●▽●▽●▽●▽●▽●▽●▽●
# Cores ACI: 1=Vermelho, 3=Verde, 4=Ciano, 5=Azul, 6=Magenta, 8,9,10...
# --- Paleta de cores para as camadas PECA_EQ ---
# Modifique estas constantes para alterar as cores das camadas geradas.
COR_CHAPA_BASE = 5  # Azul (para a maior peça, PECA_EQ_1)
CORES_SECUNDARIAS = [3, 1, 3, 8, 9, 10, 11, 12, 13, 14, 15] # Magenta, Ciano, Verde, etc.

PECA_EQ_LAYER_COLORS = [COR_CHAPA_BASE] + CORES_SECUNDARIAS
PECA_EQ_LAYER_PREFIX = "PECA_EQ"
# ●▽●▽●▽●▽●▽●▽●▽●●▽●▽●▽●▽●▽●▽●▽●●▽●▽●▽●▽●▽●▽●▽●●▽●▽●▽●▽●▽●▽●▽●●▽●▽●▽●▽▽ 
# --- FUNÇÕES AUXILIARES GERAIS ---

def get_aci_color_name(aci_index):
    color_map = {1: "Vermelho", 2: "Amarelo", 3: "Verde", 4: "Ciano", 5: "Azul", 6: "Magenta"}
    return color_map.get(aci_index, f"ACI {aci_index}")

def is_hole_side_view(entity, known_diameters: set) -> tuple[bool, float]:
    """
    Verifica se uma entidade (LWPOLYLINE, etc. ou INSERT) é uma vista lateral de um furo.
    A lógica agora checa se a LARGURA ou a ALTURA da entidade corresponde a um diâmetro conhecido.
    Retorna uma tupla: (True/False, dimensão_correspondente_ao_diâmetro).
    """
    entity_type = entity.dxftype()
    
    try:
        bbox = BoundingBox()
        
        if entity_type in ('LWPOLYLINE', 'POLYLINE', 'TRACE'):
            bbox = BoundingBox(entity.vertices_in_wcs())
        
        elif entity_type == 'INSERT':
            virtual_ents = list(entity.virtual_entities())
            if not virtual_ents:
                return False, 0.0
            
            for v_ent in virtual_ents:
                try:
                    if hasattr(v_ent, 'vertices_in_wcs'):
                        bbox.extend(v_ent.vertices_in_wcs())
                except (RuntimeError, DXFValueError):
                    continue
        else:
            return False, 0.0

        if not bbox.has_data:
            return False, 0.0
        
        width = bbox.size.x
        height = bbox.size.y

        # --- LÓGICA PRINCIPAL ALTERADA ---
        # Não checa mais se é um quadrado.
        # Checa se a largura OU a altura correspondem a um diâmetro conhecido.
        rounded_width = round(width)
        rounded_height = round(height)

        if rounded_width in known_diameters:
            return True, width  # Retorna a dimensão que correspondeu
        
        if rounded_height in known_diameters:
            return True, height # Retorna a dimensão que correspondeu
            
    except (AttributeError, IndexError, DXFValueError, TypeError):
        return False, 0.0
        
    return False, 0.0

def pre_process_holes_and_side_views(doc, msp) -> set:
    """
    Identifica furos (círculos) e suas vistas laterais (retângulos ou blocos) e os move para uma camada dedicada.
    """
    print("\n--- Pré-processamento: Identificando furos e vistas laterais ---")
    
    HOLE_LAYER_NAME = "FUROS_E_VISTAS"
    HOLE_LAYER_COLOR = COLOR_RED
    
    if HOLE_LAYER_NAME not in doc.layers:
        doc.layers.new(name=HOLE_LAYER_NAME, dxfattribs={'color': HOLE_LAYER_COLOR})

    processed_handles = set()
    circles_by_diameter = defaultdict(list)
    side_view_candidates = []

    for entity in msp:
        if entity.dxftype() == 'CIRCLE':
            diameter = round(entity.dxf.radius * 2)
            circles_by_diameter[diameter].append(entity)
        elif entity.dxftype() in ('LWPOLYLINE', 'POLYLINE', 'TRACE', 'INSERT'):
            side_view_candidates.append(entity)
            
    if not circles_by_diameter:
        print(" - Nenhum furo (círculo) encontrado. Pulando esta etapa.")
        return processed_handles
    
    known_diameters = set(circles_by_diameter.keys())
    print(f" - Diâmetros de furos encontrados no desenho: {sorted(list(known_diameters))}")

    matched_side_views = defaultdict(list)
    for entity in side_view_candidates:
        is_side_view, dimension = is_hole_side_view(entity, known_diameters)
        if is_side_view:
            matched_diameter = round(dimension)
            if matched_diameter in known_diameters:
                 matched_side_views[matched_diameter].append(entity)

    moved_count = 0
    for diameter, circle_list in circles_by_diameter.items():
        for circle in circle_list:
            if circle.dxf.handle not in processed_handles:
                circle.dxf.layer = HOLE_LAYER_NAME
                processed_handles.add(circle.dxf.handle)
                moved_count += 1
        
        if diameter in matched_side_views:
            side_views = matched_side_views[diameter]
            print(f"   - Associando {len(side_views)} vistas laterais ao diâmetro {diameter}.")
            for sv_entity in side_views:
                if sv_entity.dxf.handle not in processed_handles:
                    sv_entity.dxf.layer = HOLE_LAYER_NAME
                    processed_handles.add(sv_entity.dxf.handle)
                    moved_count += 1
    
    if moved_count > 0:
        print(f" - Total de {moved_count} entidades (furos e vistas) movidas para a camada '{HOLE_LAYER_NAME}'.")
        
    return processed_handles

def organize_existing_layers(doc, msp):
    """
    Cria uma nova estrutura de layers e move as entidades dos layers antigos para os novos.
    """
    print("\n--- Reorganizando layers existentes para nova estrutura ---")
    map_upper = {k.upper(): v for k, v in LAYER_ORGANIZATION_MAP.items()}
    moved_count = 0

    for old_layer_name_upper, (new_layer_name, new_color) in map_upper.items():
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': new_color})
        
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
    
    for _, (new_layer_name, new_color) in LAYER_ZERO_SUBCLASSIFICATION.items():
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': new_color})

    entities_on_layer_zero = msp.query("*[layer=='0']")
    
    for entity in entities_on_layer_zero:
        dxftype = entity.dxftype()
        for entity_types, (new_layer_name, _) in LAYER_ZERO_SUBCLASSIFICATION.items():
            if dxftype in entity_types:
                entity.dxf.layer = new_layer_name
                moved_count += 1
                break 

    if moved_count > 0:
        print(f" - {moved_count} entidades do layer '0' foram movidas para layers subclassificados.")
    else:
        print("Nenhuma entidade correspondente às regras de subclassificação foi encontrada no layer '0'.")

def organize_remaining_layer_zero_entities(doc, msp):
    """
    Move todas as entidades restantes no layer '0' para um novo layer 'Linhas de chamadas'.
    """
    print("\n--- Organizando entidades restantes no Layer '0' ---")
    new_layer_name = "Linhas de chamadas"
    moved_count = 0
    
    remaining_entities = msp.query("*[layer=='0']")
    
    if remaining_entities:
        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': COLOR_YELLOW})

        for entity in remaining_entities:
            entity.dxf.layer = new_layer_name
            moved_count += 1
        
    if moved_count > 0:
        print(f" - {moved_count} entidades restantes do layer '0' foram movidas para o layer '{new_layer_name}'.")
    else:
        print("Nenhuma entidade restou no layer '0' para ser organizada.")

def is_rectangular(entity, tolerance=0.01) -> bool:
    """
    Verifica se uma entidade (LWPOLYLINE/POLYLINE) é um retângulo.
    Retorna True se for retangular e não quadrado, False caso contrário.
    """
    if entity.dxftype() not in ('LWPOLYLINE', 'POLYLINE'):
        return False

    try:
        bbox = BoundingBox(entity.vertices_in_wcs())
        if not bbox.has_data:
            return False
        
        width = bbox.size.x
        height = bbox.size.y
        
        if not math.isclose(width, height, rel_tol=tolerance):
            return True 
    except (AttributeError, IndexError):
        return False
    return False

def is_long_and_thin(entity, aspect_ratio_threshold=4.0) -> tuple[bool, float]:
    """
    Verifica se uma entidade (LWPOLYLINE/POLYLINE) é longa e fina.
    Retorna uma tupla: (True/False, comprimento_se_verdadeiro).
    """
    if entity.dxftype() not in ('LWPOLYLINE', 'POLYLINE'):
        return False, 0.0

    try:
        bbox = BoundingBox(entity.vertices_in_wcs())
        if not bbox.has_data:
            return False, 0.0
        
        width = bbox.size.x
        height = bbox.size.y
        
        if min(width, height) > 0:
            aspect_ratio = max(width, height) / min(width, height)
            if aspect_ratio >= aspect_ratio_threshold:
                return True, max(width, height) 
    except (AttributeError, IndexError, ZeroDivisionError):
        return False, 0.0
    return False, 0.0

def process_drawing_by_area(filepath: str, precision: int):
    """
    Executa as rotinas de otimização no desenho: pré-processa furos, reorganiza, subclassifica e agrupa peças por área/perímetro.
    """
    doc, msp = _load_drawing(filepath)
    if not doc:
        return
    
    set_lhidden_to_red(doc)  #Chamada da funcao para definir o L-HIDDEN para vermelho

    processed_handles = pre_process_holes_and_side_views(doc, msp)
    _run_common_organization_tasks(doc, msp)    
    _analyze_and_group_by_area(doc, msp, precision, filepath, processed_handles)

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

def _analyze_and_group_by_area(doc, msp, precision, filepath: str, processed_handles: set):
    """Agrupa peças equivalentes com base na área e perímetro."""
    print("\n--- Analisando geometrias para encontrar peças equivalentes ---")
    entities_by_properties = defaultdict(list)
    unclosed_entities = []
    print(f"Analisando todas as {len(msp)} entidades do desenho com precisão de {precision} casas decimais...")

    for entity in msp:
        if entity.dxf.handle in processed_handles:
            continue
        if not hasattr(entity, 'dxftype'):
            continue
        properties = get_closed_entity_properties(entity)
        if properties:
            dxftype, area, perimeter = properties
            if dxftype == 'CIRCLE':
                diameter = round(2 * math.sqrt(area / math.pi))
                prop_key = (dxftype, diameter)
            else:
                prop_key = (dxftype, round(area, precision), round(perimeter, precision))
            entities_by_properties[prop_key].append(entity)
        else:
            unclosed_entities.append(entity)

    print("\n--- Associando enrijecedores (linhas) a furos (círculos) por diâmetro ---")
    circle_diameter_map = {
        prop_key[1]: entities
        for prop_key, entities in entities_by_properties.items()
        if prop_key[0] == 'CIRCLE'
    }
    stiffener_groups_to_remove = []
    for prop_key, entities in list(entities_by_properties.items()):
        if prop_key[0] not in ('LWPOLYLINE', 'POLYLINE'):
            continue
        is_stiffener, length = is_long_and_thin(entities[0])
        if is_stiffener:
            rounded_length = round(length)
            if rounded_length in circle_diameter_map:
                print(f"   - Encontrado grupo de enrijecedores (comprimento: {rounded_length}). Associando ao grupo de furos correspondente...")
                circle_diameter_map[rounded_length].extend(entities)
                stiffener_groups_to_remove.append(prop_key)
    for key in stiffener_groups_to_remove:
        del entities_by_properties[key]

    if not entities_by_properties:
        print("Nenhuma forma fechada válida foi encontrada para agrupar.")
        _save_drawing(doc, filepath)
        return
        
    print(f"\nForam encontrados {len(entities_by_properties)} grupos distintos de peças com geometrias equivalentes.")
    
    sorted_groups = sorted(
        entities_by_properties.items(),
        key=lambda item: (
            (item[0][1] if item[0][0] == 'CIRCLE' else item[0][1] * len(item[1])),
            (0 if item[0][0] == 'CIRCLE' else item[0][2])
        ),
        reverse=True
    )
    
    print("\n--- Verificando contexto espacial (peças internas vs. externas) ---")
    if len(sorted_groups) > 1:
        main_plate_group_key, main_plate_entities = sorted_groups[0]
        if main_plate_group_key[0] != 'CIRCLE':
            main_plate_bbox = BoundingBox()
            for entity in main_plate_entities:
                try:
                    main_plate_bbox.extend(entity.vertices_in_wcs())
                except (AttributeError, TypeError, DXFValueError):
                    pass
            if main_plate_bbox.has_data:
                print(f" - Peça principal (futura PECA_EQ_1) identificada. Área de verificação definida.")
                internal_groups = []
                external_groups = []
                for group in sorted_groups[1:]:
                    representative_entity = group[1][0]
                    center = obter_centro_geometrico(representative_entity)
                    if center and representative_entity.dxftype() in ('LWPOLYLINE', 'POLYLINE') and representative_entity.is_closed:
                        if main_plate_bbox.inside(center):
                            internal_groups.append(group)
                        else:
                            external_groups.append(group)
                    else:
                        external_groups.append(group)
                final_sorted_groups = [sorted_groups[0]] + external_groups + internal_groups
                print(f" - Reordenação concluída: 1 peça principal, {len(external_groups)} grupos externos, {len(internal_groups)} grupos internos.")
            else:
                final_sorted_groups = sorted_groups
                print(" - Aviso: Não foi possível definir a área da peça principal. Usando a ordenação padrão por área.")
        else:
            final_sorted_groups = sorted_groups
            print(" - Peça principal é um círculo. Pulando a verificação espacial.")
    else:
        final_sorted_groups = sorted_groups

    # --- LÓGICA ESPECIAL (RETÂNGULO) ---
    if len(final_sorted_groups) >= 6:
        first_group_entities = final_sorted_groups[0][1]
        representative_entity = first_group_entities[0]

        if is_rectangular(representative_entity):
            print("\n--- Lógica Especial: PECA_EQ_1 é retangular. Mesclando PECA_EQ_6 com PECA_EQ_1. ---")
            group_6_key, group_6_entities = final_sorted_groups[5]
            first_group_entities.extend(group_6_entities)
            print(f" - {len(group_6_entities)} peças do grupo 6 (área ~{group_6_key[1]}) foram movidas para o grupo da PECA_EQ_1.")
            del final_sorted_groups[5]
    
    layer_counter = 0
    non_circle_counter = 0
    
    for prop_key, entities in final_sorted_groups:
        layer_counter += 1
        new_layer_name = f"{PECA_EQ_LAYER_PREFIX}_{layer_counter}"
        
        entity_type = prop_key[0]
        is_like_a_circle = False
        if entity_type == 'CIRCLE':
            is_like_a_circle = True
            print(f" - Grupo {layer_counter}: Criando layer '{new_layer_name}' para {len(entities)} peças do tipo 'CIRCLE' com diâmetro ~{prop_key[1]}. Cor ACI: {COLOR_RED}")
        else:
            area_key = prop_key[1]
            perimeter_key = prop_key[2]
            print(f" - Grupo {layer_counter}: Criando layer '{new_layer_name}' para {len(entities)} peças do tipo '{entity_type}' com área ~{area_key} e perímetro ~{perimeter_key}. Cor ACI: {PECA_EQ_LAYER_COLORS[non_circle_counter % len(PECA_EQ_LAYER_COLORS)]}")
            isoperimetric_ratio = (4 * math.pi * area_key) / (perimeter_key**2)
            if isoperimetric_ratio > 0.98: 
                is_like_a_circle = True

        if is_like_a_circle:
            color_index = COLOR_RED
        else:
            color_index = PECA_EQ_LAYER_COLORS[non_circle_counter % len(PECA_EQ_LAYER_COLORS)]
            non_circle_counter += 1

        if new_layer_name not in doc.layers:
            doc.layers.new(name=new_layer_name, dxfattribs={'color': color_index})
        for entity in entities:
            entity.dxf.layer = new_layer_name

    print("\n--- Redirecionando layers de vistas diferentes ---")
    source_layer_name = f"{PECA_EQ_LAYER_PREFIX}_5"
    target_layer_name = f"{PECA_EQ_LAYER_PREFIX}_1"

    if source_layer_name in doc.layers and target_layer_name in doc.layers:
        entities_to_move = msp.query(f'*[layer=="{source_layer_name}"]')
        count = len(entities_to_move)
        if count > 0:
            print(f" - Movendo {count} peças do layer '{source_layer_name}' para o layer '{target_layer_name}'.")
            for entity in entities_to_move:
                entity.dxf.layer = target_layer_name
            
            try:
                doc.layers.remove(source_layer_name)
                print(f" - Layer '{source_layer_name}' removido.")
            except DXFValueError:
                print(f" - Aviso: Não foi possível remover o layer '{source_layer_name}'.")

    source_layer_furos = "FUROS_E_VISTAS"
    if source_layer_furos in doc.layers and target_layer_name in doc.layers:
        entities_to_move = msp.query(f'*[layer=="{source_layer_furos}"]')
        count = len(entities_to_move)
        if count > 0:
            print(f" - Movendo {count} peças do layer '{source_layer_furos}' para o layer '{target_layer_name}'.")
            for entity in entities_to_move:
                entity.dxf.layer = target_layer_name
            
            try:
                doc.layers.remove(source_layer_furos)
                print(f" - Layer '{source_layer_furos}' removido.")
            except DXFValueError:
                print(f" - Aviso: Não foi possível remover o layer '{source_layer_furos}'.")

    print("\n--- Aplicando Cores Específicas (Overrides) ---")
    
    # Regra: A camada PECA_EQ_6 deve ser sempre Magenta.
    layer_to_colorize = f"{PECA_EQ_LAYER_PREFIX}_6"
    
    if layer_to_colorize in doc.layers:
        layer = doc.layers.get(layer_to_colorize)
        layer.dxf.color = COLOR_MAGENTA
        print(f" - Override aplicado: Cor da camada '{layer_to_colorize}' definida para Magenta.")
    else:
        print(f" - Camada '{layer_to_colorize}' não encontrada para override de cor (pode ter sido mesclada ou não existe).")

    _save_drawing(doc, filepath)

def obter_centro_geometrico(entity):
    try:
        bbox = BoundingBox(entity.vertices_in_wcs())
        return bbox.center.xy
    except (AttributeError, TypeError, ValueError, DXFValueError):
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

    if dx == 'TRACE' or dx == 'POLYLINE' or dx == 'LWPOLYLINE':
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
        print(f"   + Criando nova camada '{layer_name}' com a cor {get_aci_color_name(color)}.")
        doc.layers.new(name=layer_name, dxfattribs={'color': color})
    # else:
    #     doc.layers.get(layer_name).dxf.color = color

def set_layer0_to_yellow(doc):
    layer_name = '0'
    try:
        if layer_name not in doc.layers:
            print(f"   + Criando camada '{layer_name}' com a cor {get_aci_color_name(COLOR_LAYER_0)}.")
            doc.layers.new(name=layer_name, dxfattribs={'color': COLOR_LAYER_0})
        else:
            doc.layers.get(layer_name).dxf.color = COLOR_LAYER_0
            print(f"   * Camada '{layer_name}' atualizada para cor {get_aci_color_name(COLOR_LAYER_0)}.")
    except Exception as e:
        print(f"Aviso: não foi possível ajustar a cor da camada '0': {e}")

def _normalize_layer_name(name: str) -> str:
    if not name:
        return ''
    nfkd = unicodedata.normalize('NFKD', name)
    only_ascii = ''.join([c for c in nfkd if not unicodedata.combining(c)])
    cleaned = only_ascii.replace(' ', '').replace('-', '').replace('_', '').lower()
    return cleaned

def set_g_symbol_to_yellow(doc):
    candidates = ['G-SYMBOL', 'G SIMBOLO', 'G_SIMBOLO', 'GSYMBOL']
    normalized_candidates = {_normalize_layer_name(c): c for c in candidates}
    found = False
    try:
        for layer in doc.layers:
            nl = _normalize_layer_name(layer.dxf.name)
            if nl in normalized_candidates:
                layer.dxf.color = COLOR_LAYER_0
                print(f"   * Camada existente '{layer.dxf.name}' atualizada para cor {get_aci_color_name(COLOR_LAYER_0)}.")
                found = True
        if not found:
            default_name = 'G SIMBOLO'
            ensure_layer(doc, default_name, COLOR_LAYER_0)
    except Exception as e:
        print(f"Aviso: erro ao procurar camadas G-SYMBOL: {e}")

def set_lhidden_to_red(doc):
    """
    Encontra a camada L-HIDDEN e define sua cor para vermelho.
    Se a camada não existir, ela será criada com a cor vermelha.
    """
    layer_name_upper = "L-HIDDEN"
    found_layer = None

    try:
        # Itera sobre as camadas para encontrar a correspondente, ignorando maiúsculas/minúsculas
        for layer in doc.layers:
            if layer.dxf.name.upper() == layer_name_upper:
                found_layer = layer
                break # Encontrou a camada, pode parar de procurar

        if found_layer:
            # Cenário 1: A camada existe, apenas atualiza a cor.
            found_layer.dxf.color = COLOR_RED
            print(f"   * Camada existente '{found_layer.dxf.name}' atualizada para cor Vermelha.")
        else:
            # Cenário 2: A camada não existe, então a criamos.
            doc.layers.new(name="L-HIDDEN", dxfattribs={'color': COLOR_RED})
            print(f"   * Camada 'L-HIDDEN' não encontrada. Criando nova camada na cor Vermelha.")

    except Exception as e:
        print(f"Aviso: erro ao tentar ajustar a cor da camada L-HIDDEN: {e}")

def process_cotas_and_texts(doc, msp, processed_handles):
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
    centers = []
    for ent in msp.query('DIMENSION'):
        c = obter_centro_geometrico(ent)
        if c:
            centers.append(c)
    return centers

def move_nearby_unclosed_lines_to_setas(doc, msp, alvos_chapa, processed_handles, arrow_proximity, raio_de_busca):
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

    processed_handles = pre_process_holes_and_side_views(doc, msp)

    print("\nIniciando reestruturação com base em texto (Método 2).")
    set_layer0_to_yellow(doc)
    set_g_symbol_to_yellow(doc)
    set_lhidden_to_red(doc)
    
    print("\n--- Fase 1: Identificando sistemas (Perfis, Chumbadores, Eixos) ---")
    for keyword, (layer_name, color) in SEMANTIC_LAYERS.items():
        ensure_layer(doc, layer_name, color)

    for entity in msp:
        if entity.dxf.handle in processed_handles:
            continue
            
        original_layer = entity.dxf.layer.lower()
        eh_tracejado = hasattr(entity.dxf, 'linetype') and entity.dxf.linetype.lower() not in ['continuous', 'byblock', 'bylayer']

        for keyword, (target_layer, _) in SEMANTIC_LAYERS.items():
            if (keyword == 'eixo' and eh_tracejado) or keyword in original_layer:
                entity.dxf.layer = target_layer
                entity.dxf.color = 256 # BYLAYER
                processed_handles.add(entity.dxf.handle)
                break

    dimension_centers = collect_dimension_centers(msp)

    print("\n--- Fase 2: Mapeando e agrupando Chapas por texto ---")
    alvos_chapa = defaultdict(list)
    for entity in msp.query('TEXT MTEXT ATTRIB'):
        if entity.dxf.handle in processed_handles:
            continue

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

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Otimizador de Layers DXF")
        self.geometry("700x600")

        self.filepath = tk.StringVar()
        self.analysis_method = tk.StringVar(value="1")
        self.precision = tk.StringVar(value="0")
        self.queue = queue.Queue()

        self.create_widgets()
        self.redirect_stdout()

    def create_widgets(self):
        main_frame = ttk.Frame(self, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        file_frame = ttk.LabelFrame(main_frame, text="Arquivo DXF", padding="10")
        file_frame.pack(fill=tk.X, pady=5)
        file_frame.columnconfigure(1, weight=1)

        ttk.Label(file_frame, text="Caminho:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(file_frame, textvariable=self.filepath).grid(row=0, column=1, sticky=tk.EW, padx=5, pady=5)
        ttk.Button(file_frame, text="Procurar...", command=self.browse_file).grid(row=0, column=2, padx=5, pady=5)

        method_frame = ttk.LabelFrame(main_frame, text="Método de Análise", padding="10")
        method_frame.pack(fill=tk.X, pady=5)

        ttk.Radiobutton(method_frame, text="Análise por Área (peças com geometria idêntica)", variable=self.analysis_method, value="1", command=self.toggle_precision).pack(anchor=tk.W)
        self.precision_frame = ttk.Frame(method_frame, padding="0 0 0 20")
        self.precision_frame.pack(fill=tk.X)
        ttk.Label(self.precision_frame, text="Precisão (casas decimais):").pack(side=tk.LEFT, padx=5)
        ttk.Entry(self.precision_frame, textvariable=self.precision, width=5).pack(side=tk.LEFT)

        ttk.Radiobutton(method_frame, text="Análise por Texto (identifica 'CHAPA XXX')", variable=self.analysis_method, value="2", command=self.toggle_precision).pack(anchor=tk.W)

        self.process_button = ttk.Button(main_frame, text="Processar Desenho", command=self.start_processing)
        self.process_button.pack(pady=10, fill=tk.X)

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
            while True:
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