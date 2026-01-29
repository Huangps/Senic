import matplotlib.pyplot as plt

def draw_grid(rows, cols, cell_text=None, filename='grid.png',
              cell_size=1.0, fontsize=14, circle_radius=0.35):
    """
    绘制网格并支持带圆圈的彩色符号。
    参数：
        rows, cols: 行列数
        cell_text: dict，键为 (row, col)，值为 dict：
                    {"text": "I", "color": "red", "circle": True}
        filename: 输出文件名
        cell_size: 每个格子视觉大小
        fontsize: 字体大小
        circle_radius: 圆圈半径
    """
    if cell_text is None:
        cell_text = {}

    fig_width = cols * cell_size * 0.6 + 1.8
    fig_height = rows * cell_size * 0.6 + 1.8
    fig, ax = plt.subplots(figsize=(fig_width, fig_height))
    ax.set_xlim(0, cols)
    ax.set_ylim(0, rows)
    ax.invert_yaxis()
    ax.set_aspect('equal')
    ax.axis('off')

    # 绘制网格线
    for c in range(cols + 1):
        ax.plot([c, c], [0, rows], color='black', linewidth=1)
    for r in range(rows + 1):
        ax.plot([0, cols], [r, r], color='black', linewidth=1)

    # 列号
    for c in range(cols):
        ax.text(c + 0.5, -0.35, str(c), ha='center', va='top', fontsize=fontsize)
    # 行号
    for r in range(rows):
        ax.text(-0.35, r + 0.5, str(r), ha='right', va='center', fontsize=fontsize)

    # 绘制内容
    for (r, c), spec in cell_text.items():
        if not (0 <= r < rows and 0 <= c < cols):
            continue
        text = spec.get("text", "")
        color = spec.get("color", "black")
        circle = spec.get("circle", False)

        if circle:
            circle_patch = plt.Circle((c + 0.5, r + 0.5), circle_radius,
                                      edgecolor=color, facecolor='none', linewidth=2)
            ax.add_patch(circle_patch)
        ax.text(c + 0.5, r + 0.5, text, ha='center', va='center',
                fontsize=fontsize, color=color, fontweight='bold')

    plt.savefig(filename, bbox_inches='tight', dpi=150)
    plt.close(fig)
    print(f"✅ 已保存图片: {filename}")

# 示例使用
if __name__ == "__main__":
    rows = 2
    cols = 10
    cells = {
        (0, 0): {"text": "I", "color": "blue", "circle": True},
        (1, 0): {"text": "G", "color": "green", "circle": True},
        (1, 9): {"text": "G", "color": "red", "circle": True},
        (1, 3): {"text": "x", "color": "red", "circle": False},
        (1, 5): {"text": "+", "color": "green", "circle": False}
    }
    draw_grid(rows, cols, cell_text=cells, filename="grid_colored.png")
