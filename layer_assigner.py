# -*- coding: utf-8 -*-

"""
Script para automação de tarefas em desenhos DXF. Executa quatro funções principais:
1. Reorganiza entidades de layers específicos para uma nova estrutura de layers padronizada.
2. Subclassifica entidades do layer '0' (TEXT, HATCH) para novos layers específicos.
3. Move as entidades restantes no layer '0' para um novo layer 'Linhas de chamadas'.
4. Analisa e agrupa entidades fechadas idênticas em novos layers de 'peças equivalentes'.

Persona: Desenvolvedor Python Sênior
Projeto: Ferramenta de automação para desenhos de estruturas metálicas.
Revisão: 19.0 - 2025-10-06 (Adicionada função para mover entidades restantes do layer '0')
"""

import ezdxf
import os
import math
from collections import defaultdict
from ezdxf.path import make_path
from ezdxf.math import area as path_area, Vec3
from ezdxf import DXFValueError

# --- CONFIGURAÇÕES ---
# 1 = Vermelho, 2 = Amarelo, 3 = Verde, 4 = Ciano, 5 = Azul, 6 = Magenta, 7 = Branco/Preto
COLOR_RED = 1
COLOR_YELLOW = 2
COLOR_GREEN = 3

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

# Configurações para a análise de peças equivalentes
PECA_EQ_LAYER_COLORS = [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15]
PECA_EQ_LAYER_PREFIX = "PECA_EQ"


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

def process_drawing(filepath: str, precision: int):
    """
    Executa as rotinas de otimização no desenho: reorganiza, subclassifica e agrupa peças.
    """
    try:
        print(f"Carregando o desenho: {os.path.basename(filepath)}...")
        doc = ezdxf.readfile(filepath)
        msp = doc.modelspace()
    except Exception as e:
        print(f"Erro ao carregar o arquivo DXF: {e}")
        return

    # Tarefa 1: Reorganizar layers existentes para uma nova estrutura
    organize_existing_layers(doc, msp)
    
    # Tarefa 2: Subclassificar entidades do layer '0'
    subclassify_layer_zero(doc, msp)

    # Tarefa 3: Organizar o que sobrou no layer '0'
    organize_remaining_layer_zero_entities(doc, msp)

    # Tarefa 4: Encontrar e agrupar peças equivalentes
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
            color_index = PECA_EQ_LAYER_COLORS[(layer_counter - 1) % len(PECA_EQ_LAYER_COLORS)]
            entity_type, area_key, perimeter_key = prop_key
            print(f" - Grupo {layer_counter}: Criando layer '{new_layer_name}' para {len(entities)} peças do tipo '{entity_type}' com área ~{area_key} e perímetro ~{perimeter_key}")

            if new_layer_name not in doc.layers:
                doc.layers.new(name=new_layer_name, dxfattribs={'color': color_index})
            for entity in entities:
                entity.dxf.layer = new_layer_name

    base, ext = os.path.splitext(filepath)
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

def main():
    """
    Função principal que gerencia a interface com o usuário no console.
    """
    print("---------------------------------------------------------------------")
    print("---      Ferramenta de Otimização de Layers para DXF              ---")
    print("---------------------------------------------------------------------")
    
    filepath = ""
    while True:
        filepath_input = input("Por favor, arraste o arquivo DXF para cá ou cole o caminho e pressione Enter:\n> ").strip()
        filepath = filepath_input.strip('"\'')
        if filepath and os.path.exists(filepath):
            break
        else:
            print("Arquivo não encontrado. Por favor, forneça um caminho válido.")

    precision = 2
    while True:
        try:
            precision_input = input(f"Digite a precisão para análise de peças (casas decimais, padrão é {precision}, pressione Enter para usar):\n> ").strip()
            if not precision_input:
                break 
            precision = int(precision_input)
            if precision >= 0:
                break
            else:
                print("Por favor, digite um número positivo.")
        except ValueError:
            print("Entrada inválida. Por favor, digite um número inteiro.")

    process_drawing(filepath, precision)
    input("\nPressione Enter para sair.")

if __name__ == "__main__":
    main()

