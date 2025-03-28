# Voxel World Prototype

A simple voxel engine prototype built with Three.js demonstrating procedural terrain generation, block placement/breaking, a day/night cycle, and a viewmodel torch with particle effects.

## Features

*   **Procedural Voxel Terrain:** Infinite terrain generated using multi-octave value noise.
*   **Chunk System:** World is divided into chunks, only loading chunks within the render distance around the player.
*   **Instanced Rendering:** Uses `InstancedMesh` for efficient rendering of many blocks.
*   **Block Interaction:**
    *   Left-click to break blocks.
    *   Right-click to place blocks (currently selected type shown bottom-left).
*   **Procedural Textures:** Block textures are generated dynamically using the Canvas API, reducing the need for external image files. Includes Grass, Dirt, Stone, Wood (with rings/grain), and Leaves (with transparency).
*   **Player Movement:** Standard FPS controls (WASD), jumping (Space), and basic flying (toggle with F, Space/Shift to ascend/descend). Includes basic collision detection and resolution.
*   **Day/Night Cycle:** Smooth transition between dawn, day, dusk, and night with corresponding changes in:
    *   Sky color
    *   Fog color and density
    *   Sun/Moon light intensity and color
    *   Hemisphere light intensity and color
    *   Starfield visibility
*   **Animated Torch:** A torch model attached to the camera (viewmodel) with:
    *   Flickering point light source.
    *   Animated flame mesh (scaling/position flicker).
    *   Simple particle system for sparks/embers rising from the flame.
    *   Subtle viewmodel bobbing when moving.
*   **Pointer Lock Controls:** Uses Pointer Lock API for mouse look.
*   **Basic UI:** Displays player position, chunk coordinates, time of day, flight/ground status, and selected block type.

## Controls

*   **W, A, S, D:** Move Forward / Left / Backward / Right
*   **Mouse:** Look Around
*   **Left Click:** Break Block
*   **Right Click:** Place Block
*   **SPACE:** Jump (when on ground) / Fly Up (when flying)
*   **SHIFT:** Fly Down (when flying) / Crouch (Functionality TBD)
*   **F:** Toggle Fly Mode On/Off
*   **1:** Select Stone Block
*   **2:** Select Dirt Block
*   **3:** Select Grass Block
*   **4:** Select Wood Block
*   **5:** Select Leaves Block
*   **ESC:** Release Mouse Lock / Pause (Show Instructions)

## Technology Used

*   **Three.js (r162):** Core 3D library. Imported via ES Modules and `importmap`.
*   **JavaScript (ES Modules):** Application logic.
*   **HTML5:** Structure and Canvas container.
*   **CSS3:** Styling for UI elements.

## How to Run

Because this project uses ES Modules (`import` statements), you **cannot** simply open the `index.html` file directly in your browser using the `file:///` protocol due to browser security restrictions (CORS policy).

You need to serve the files using a local web server. Here are a few easy ways:

1.  **Using Python:**
    *   Open your terminal or command prompt.
    *   Navigate to the directory containing `index.html`, `style.css`, and `script.js`.
    *   Run the command: `python -m http.server` (for Python 3) or `python -m SimpleHTTPServer` (for Python 2).
    *   Open your web browser and go to `http://localhost:8000`.

2.  **Using Node.js / `npx`:**
    *   Make sure you have Node.js installed.
    *   Open your terminal or command prompt.
    *   Navigate to the project directory.
    *   Run the command: `npx serve`
    *   The terminal will output the local address (usually `http://localhost:3000`). Open this address in your browser.

3.  **Using VS Code Live Server Extension:**
    *   If you are using Visual Studio Code, install the "Live Server" extension.
    *   Open the project folder in VS Code.
    *   Right-click on the `index.html` file in the explorer panel and select "Open with Live Server".

Once served, click the instructions box to lock the pointer and start playing.

## File Structure
