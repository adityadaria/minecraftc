import * as THREE from 'three';
import { PointerLockControls } from 'three/addons/controls/PointerLockControls.js';

// --- Config ---
const CHUNK_SIZE_X = 16;
const CHUNK_SIZE_Z = 16;
const CHUNK_SIZE_Y = 128;
const WORLD_HEIGHT = CHUNK_SIZE_Y;
const BLOCK_TYPE = { AIR: 0, GRASS: 1, DIRT: 2, STONE: 3, WOOD: 4, LEAVES: 5 };
const BLOCK_NAMES = { 0: 'AIR', 1: 'GRASS', 2: 'DIRT', 3: 'STONE', 4: 'WOOD', 5: 'LEAVES' };
const RENDER_DISTANCE = 6; // In chunks
const MAX_RAYCAST_DISTANCE = 6; // In blocks
const TEXTURE_SIZE = 32; // Pixels for procedural textures
const DAY_CYCLE_SECONDS = 60 * 5; // 5 minutes for a full day/night cycle

// --- Game State ---
let scene, camera, renderer, controls, clock, sunLight, moonLight, hemisphereLight;
let sunMesh, moonMesh, torchMesh, torchLight, flameMesh;
// Particle System Variables
let particleSystem, particleGeometry, particleMaterial;
let particlePositions, particleVelocities, particleLifetimes;
const particleCount = 100;
const particleSpawnRadius = 0.03;
const particleBaseLifetime = 0.8; // seconds
const particleLifetimeVariance = 0.3;
const particleGravity = 0.15;
const particleBaseVelocityY = 0.2;
const particleVelocityVariance = 0.1;

const worldChunks = new Map(); // Stores chunk data { `${x},${z}`: chunkDataArray }
const chunkMeshes = new Map(); // Stores chunk mesh groups { `${x},${z}`: { typeId: InstancedMesh, ... } }
const loadedMaterials = {}; // Stores generated block materials
const textureCache = {}; // Caches generated CanvasTextures
let gameTime = 0; // Represents time of day (0.0 to 1.0)
let starsDiv; // Reference to the star background div

const player = {
    height: 1.8, // Player eye height
    radius: 0.4, // Player collision cylinder radius
    speed: 5.0, // Ground movement speed units/sec
    flySpeed: 10.0, // Flying movement speed units/sec
    jumpVelocity: 7.0, // Initial upward velocity on jump
    velocity: new THREE.Vector3(), // Current player velocity
    direction: new THREE.Vector3(), // Input direction vector
    onGround: false, // Is the player standing on a block?
    flyMode: false, // Is flying enabled?
    currentChunk: { x: null, z: null }, // Player's current chunk coordinates
    position: new THREE.Vector3() // Player's precise position (synced with camera)
};
const gravity = 22.0; // Acceleration due to gravity units/sec^2

// Torch Animation State
let torchBobbingAngle = 0;
const torchBobbingSpeed = 8.0; // Radians per second for bobbing
const torchBobbingAmount = 0.015; // Units for bobbing
const torchBaseLightIntensity = 10.0;
const torchFlickerAmount = 0.4; // Variation amount for light intensity
const torchFlickerSpeed = 15; // Frequency of light flicker

// Input State
let moveForward = false, moveBackward = false, moveLeft = false, moveRight = false;
let moveUp = false, moveDown = false; // Used for jump/fly/crouch
let blockToPlace = BLOCK_TYPE.STONE; // Currently selected block for placement

// DOM Elements
const infoDiv = document.getElementById('info');
const blockInfoDiv = document.getElementById('blockInfo');
const raycaster = new THREE.Raycaster(); // Reusable raycaster

// --- Atmospheric Colors ---
const skyColors = { dawn: new THREE.Color(0xFFB370), day: new THREE.Color(0x87CEEB), dusk: new THREE.Color(0xFF9966), night: new THREE.Color(0x06061A) };
const groundColors = { dawn: new THREE.Color(0x99704D), day: new THREE.Color(0xB97A20), dusk: new THREE.Color(0xA35B3B), night: new THREE.Color(0x1A1A2A) };
const sunLightColors = { dawn: new THREE.Color(0xFFDAA3), day: new THREE.Color(0xFFF8D6), dusk: new THREE.Color(0xFFB87A), night: new THREE.Color(0x000000) };
const moonLightColor = new THREE.Color(0x7080B0);

// --- Noise Functions (Simple Value Noise + Octaves) ---
const noisePerm = new Uint8Array(512);
const noiseInit = () => {
    const p = new Uint8Array(256);
    for (let i = 0; i < 256; i++) p[i] = i;
    for (let i = 255; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [p[i], p[j]] = [p[j], p[i]]; // Shuffle
    }
    for (let i = 0; i < 256; i++) {
        noisePerm[i] = noisePerm[i + 256] = p[i]; // Double the array for wrapping
    }
};
const fade = (t) => t * t * t * (t * (t * 6 - 15) + 10); // Smoothstep function
const lerp = (t, a, b) => a + t * (b - a); // Linear interpolation
const valueNoise2D = (x, y, scale = 0.1) => {
    x *= scale; y *= scale;
    const X = Math.floor(x) & 255; // Integer part, wrapped to 0-255
    const Y = Math.floor(y) & 255;
    x -= Math.floor(x); // Fractional part
    y -= Math.floor(y);
    const u = fade(x); // Smoothed fractional part
    const v = fade(y);
    const p = noisePerm;
    // Hash coordinates of the 4 square corners
    const A = p[X] + Y;
    const B = p[X + 1] + Y;
    // Get pseudo-random values (gradients not needed for value noise)
    const h1 = p[p[A]]; const h2 = p[p[B]];
    const h3 = p[p[A + 1]]; const h4 = p[p[B + 1]];
    // Interpolate along x
    const n1 = lerp(u, h1 / 255, h2 / 255);
    const n2 = lerp(u, h3 / 255, h4 / 255);
    // Interpolate along y and scale to [-1, 1]
    return (lerp(v, n1, n2) * 2) - 1;
};
const octaveNoise = (x, y, octaves = 4, persistence = 0.5, lacunarity = 2.0, scale = 0.02) => {
    let total = 0;
    let frequency = 1.0;
    let amplitude = 1.0;
    let maxValue = 0; // Used for normalizing result to [-1, 1]
    for (let i = 0; i < octaves; i++) {
        total += valueNoise2D(x * frequency, y * frequency, scale) * amplitude;
        maxValue += amplitude;
        amplitude *= persistence; // Amplitude decreases with each octave
        frequency *= lacunarity; // Frequency increases with each octave
    }
    return total / maxValue; // Normalize
};

// --- Initialization ---
function init() {
    noiseInit(); // Initialize noise permutation table
    starsDiv = document.getElementById('stars');
    createStars(200); // Create star DOM elements

    // Scene setup
    scene = new THREE.Scene();
    scene.background = skyColors.day; // Initial background color
    // Fog (matches background, adjusts density based on time)
    scene.fog = new THREE.Fog(skyColors.day, RENDER_DISTANCE * CHUNK_SIZE_X * 0.4, RENDER_DISTANCE * CHUNK_SIZE_X * 1.0);

    // Camera setup
    camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, RENDER_DISTANCE * CHUNK_SIZE_X * 2.0);
    camera.position.set(CHUNK_SIZE_X / 2, WORLD_HEIGHT * 0.5 + player.height, CHUNK_SIZE_Z / 2); // Start roughly in the middle

    // Renderer setup
    renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setPixelRatio(window.devicePixelRatio); // Adjust for high-DPI screens
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.outputColorSpace = THREE.SRGBColorSpace; // Correct color handling
    renderer.shadowMap.enabled = true; // Enable shadows
    renderer.shadowMap.type = THREE.PCFSoftShadowMap; // Softer shadows
    renderer.toneMapping = THREE.ACESFilmicToneMapping; // Film-like tone mapping
    renderer.toneMappingExposure = 1.0; // Adjust exposure if needed
    document.body.appendChild(renderer.domElement); // Add canvas to page

    clock = new THREE.Clock(); // For tracking delta time

    // --- Lighting Setup ---
    // Hemisphere light (sky color, ground color, intensity)
    hemisphereLight = new THREE.HemisphereLight(skyColors.day, groundColors.day, 0.8);
    scene.add(hemisphereLight);

    // Directional sun light
    sunLight = new THREE.DirectionalLight(sunLightColors.day, 1.5);
    sunLight.castShadow = true;
    sunLight.shadow.mapSize.width = 2048; // Higher res shadow map
    sunLight.shadow.mapSize.height = 2048;
    // Define shadow camera frustum (needs to cover visible area)
    const shadowCamSize = RENDER_DISTANCE * CHUNK_SIZE_X * 1.0;
    sunLight.shadow.camera.near = 0.5;
    sunLight.shadow.camera.far = WORLD_HEIGHT + 250; // Cover world height + some margin
    sunLight.shadow.camera.left = -shadowCamSize;
    sunLight.shadow.camera.right = shadowCamSize;
    sunLight.shadow.camera.top = shadowCamSize;
    sunLight.shadow.camera.bottom = -shadowCamSize;
    sunLight.shadow.bias = -0.001; // Adjust to prevent shadow acne
    scene.add(sunLight);
    scene.add(sunLight.target); // Target is needed for positioning

    // Directional moon light (starts dim)
    moonLight = new THREE.DirectionalLight(moonLightColor, 0.0);
    moonLight.castShadow = false; // Moon doesn't cast shadows in this demo
    scene.add(moonLight);
    scene.add(moonLight.target);

    // Visual representation for Sun and Moon
    const sunGeo = new THREE.SphereGeometry(15, 16, 16);
    const sunMat = new THREE.MeshBasicMaterial({ color: 0xFFFF00, fog: false }); // Disable fog for celestial bodies
    sunMesh = new THREE.Mesh(sunGeo, sunMat);
    sunMesh.name = "Sun";
    scene.add(sunMesh);

    const moonGeo = new THREE.SphereGeometry(12, 16, 16);
    const moonMat = new THREE.MeshBasicMaterial({ color: 0xE0E0E0, fog: false });
    moonMesh = new THREE.Mesh(moonGeo, moonMat);
    moonMesh.name = "Moon";
    scene.add(moonMesh);

    // Controls setup
    setupControls(); // Assigns `controls` variable

    // World generation and rendering
    createProceduralMaterials(); // Generate textures and materials for blocks
    createTorch(); // Create the torch model, light, and particle system
    console.log("Torch and particles created.");

    updateVisibleChunks(true); // Force initial chunk loading around player
    player.position.copy(camera.position); // Sync initial player state
    gameTime = 0.26; // Start slightly after dawn
    updateAtmosphere(0); // Set initial atmospheric conditions

    // Start the main loop
    animate();
}

// --- Starfield ---
function createStars(count) {
    if (!starsDiv) return;
    starsDiv.innerHTML = ''; // Clear existing stars
    for (let i = 0; i < count; i++) {
        const star = document.createElement('div');
        star.style.position = 'absolute';
        const size = Math.random() * 1.5 + 0.5; // Star size variance
        star.style.width = `${size}px`;
        star.style.height = star.style.width;
        star.style.backgroundColor = `rgba(255, 255, 255, ${Math.random() * 0.4 + 0.6})`; // Opacity variance
        star.style.borderRadius = '50%';
        star.style.left = `${Math.random() * 100}%`; // Random position
        star.style.top = `${Math.random() * 100}%`;
        star.style.boxShadow = `0 0 ${Math.random() * 2 + 1}px rgba(255, 255, 255, 0.4)`; // Glow effect
        starsDiv.appendChild(star);
    }
}

// --- Setup Controls ---
function setupControls() {
    controls = new PointerLockControls(camera, document.body);
    const blocker = document.getElementById('blocker');
    const instructions = document.getElementById('instructions');
    const crosshair = document.getElementById('crosshair');

    instructions.addEventListener('click', () => {
        // Don't lock if it's showing an error
        if (!blocker.classList.contains('error')) {
            controls.lock();
        }
    });

    controls.addEventListener('lock', () => {
        instructions.style.display = 'none';
        blocker.style.display = 'none';
        crosshair.style.display = 'block';
    });

    controls.addEventListener('unlock', () => {
        blocker.style.display = 'flex';
        instructions.style.display = ''; // Use default display (block or initial)
        crosshair.style.display = 'none';
        // Reset movement keys on unlock
        moveForward = moveBackward = moveLeft = moveRight = moveUp = moveDown = false;
    });

    // Add the controls' object (which holds the camera) to the scene
    scene.add(controls.getObject());

    // Add global event listeners
    document.addEventListener('keydown', onKeyDown);
    document.addEventListener('keyup', onKeyUp);
    document.addEventListener('mousedown', onMouseDown);
    window.addEventListener('resize', onWindowResize);
}

// --- Texture Generation Helpers ---
// Adds simple noise pixels to a canvas context
function addNoise(ctx, width, height, intensity = 0.08, colors = ['rgba(0,0,0,0.05)', 'rgba(255,255,255,0.04)'], xOffset = 0, yOffset = 0, drawWidth = width, drawHeight = height) {
    const numPixels = Math.floor(drawWidth * drawHeight * intensity);
    for (let i = 0; i < numPixels; i++) {
        const x = xOffset + Math.random() * drawWidth;
        const y = yOffset + Math.random() * drawHeight;
        ctx.fillStyle = colors[Math.floor(Math.random() * colors.length)];
        ctx.fillRect(Math.floor(x), Math.floor(y), 1, 1);
    }
}
// Modifies a hex color slightly for variation
function varyColor(hexColor, lightnessVariation = 15, saturationVariation = 0.01) {
    // Convert hex to RGB
    let r = parseInt(hexColor.slice(1, 3), 16);
    let g = parseInt(hexColor.slice(3, 5), 16);
    let b = parseInt(hexColor.slice(5, 7), 16);

    // Apply lightness variation
    const lightAdjust = Math.floor((Math.random() - 0.5) * lightnessVariation * 2);
    r += lightAdjust; g += lightAdjust; b += lightAdjust;

    // Apply saturation variation (simplified)
    if (saturationVariation > 0) {
        const avg = (r + g + b) / 3;
        const satAdjust = (Math.random() - 0.5) * saturationVariation * 2;
        const factor = Math.abs(satAdjust);
        if (satAdjust > 0) { // Increase saturation
            r = lerp(factor, r, r + (r - avg));
            g = lerp(factor, g, g + (g - avg));
            b = lerp(factor, b, b + (b - avg));
        } else { // Decrease saturation
            r = lerp(factor, r, avg);
            g = lerp(factor, g, avg);
            b = lerp(factor, b, avg);
        }
    }

    // Clamp values and convert back to rgb string
    r = Math.max(0, Math.min(255, Math.round(r)));
    g = Math.max(0, Math.min(255, Math.round(g)));
    b = Math.max(0, Math.min(255, Math.round(b)));
    return `rgb(${r},${g},${b})`;
}

// --- Procedural Texture Generation ---
// Creates a CanvasTexture based on block type and face
function generateProceduralTexture(blockType, face = 'side') {
    const cacheKey = `${blockType}_${face}_${TEXTURE_SIZE}`;
    if (textureCache[cacheKey]) {
        return textureCache[cacheKey]; // Return cached texture if available
    }

    const canvas = document.createElement('canvas');
    canvas.width = TEXTURE_SIZE;
    canvas.height = TEXTURE_SIZE;
    const ctx = canvas.getContext('2d');
    const T = TEXTURE_SIZE; // Texture Size
    const P = T / 16; // Pixel Size (assuming 16x16 base texture units)

    // Color palette
    const colors = {
        grass_top: '#78B846', grass_top_dark: '#5E9C39', grass_top_light: '#96D15F',
        grass_side_top: '#90BB4F', grass_side_dirt: '#806044',
        dirt: '#806044', dirt_dark: '#6A5139', dirt_light: '#9A7656', dirt_pebble: '#59442F',
        stone: '#7F7F7F', stone_dark: '#6F6F6F', stone_light: '#999999', stone_crack: '#555555',
        wood_top: '#6F5A3A', wood_side: '#645132', wood_dark: '#514228', wood_ring: '#4A3E26', wood_light_grain: '#7A6441',
        leaves: '#4C7F2E', leaves_dark: '#3A6323', leaves_light: '#67A53E', leaves_gap: 'rgba(0,0,0,0)' // Transparent gap
    };

    // --- Texture drawing logic per block type ---
    switch (blockType) {
        case BLOCK_TYPE.GRASS:
            if (face === 'top') {
                // Grass top (green with variations)
                ctx.fillStyle = colors.grass_top;
                ctx.fillRect(0, 0, T, T);
                // Add some blades/texture
                for (let i = 0; i < T * T * 0.5; i++) {
                    const x = Math.random() * T; const y = Math.random() * T;
                    const w = Math.random() * P * 0.8 + P * 0.2;
                    const h = Math.random() * P * 2 + P * 0.5;
                    const angle = (Math.random() - 0.5) * Math.PI * 0.3;
                    ctx.save(); ctx.translate(x, y); ctx.rotate(angle);
                    ctx.fillStyle = Math.random() > 0.4 ? varyColor(colors.grass_top_light, 8, 0.01) : varyColor(colors.grass_top_dark, 8, 0.01);
                    ctx.fillRect(-w / 2, -h / 2, w, h); ctx.restore();
                }
                // Subtle patches
                for (let i = 0; i < T * T * 0.08; i++) {
                    ctx.fillStyle = Math.random() > 0.5 ? 'rgba(0,0,0,0.04)' : 'rgba(255,255,255,0.03)';
                    ctx.fillRect(Math.random()*T, Math.random()*T, P*1.5, P*1.5);
                }
                addNoise(ctx, T, T, 0.08);
            } else if (face === 'bottom') {
                // Grass bottom (same as dirt)
                ctx.fillStyle = colors.dirt; ctx.fillRect(0, 0, T, T);
                for (let i = 0; i < T * T * 0.12; i++) {
                    ctx.fillStyle = Math.random() > 0.5 ? varyColor(colors.dirt_dark, 12) : varyColor(colors.dirt_light, 12);
                    ctx.fillRect(Math.random() * T, Math.random() * T, Math.random()*P*1.8+P*0.8, Math.random()*P*1.8+P*0.8);
                }
                for (let i = 0; i < T * T * 0.08; i++) {
                    ctx.fillStyle = varyColor(colors.dirt_pebble, 5, 0);
                    ctx.fillRect(Math.random() * T, Math.random() * T, P*0.5, P*0.5);
                }
                addNoise(ctx, T, T, 0.20);
            } else { // Side face
                const dirtHeightRatio = 0.8; // How much of the side is dirt
                const dirtHeightPx = Math.round(T * dirtHeightRatio);
                const grassHeightPx = T - dirtHeightPx;
                const transitionHeightPx = Math.max(P, grassHeightPx * 0.4); // Grass transition zone

                // Draw dirt bottom part
                ctx.fillStyle = colors.grass_side_dirt; ctx.fillRect(0, grassHeightPx, T, dirtHeightPx);
                for (let i = 0; i < T * dirtHeightPx * 0.08; i++) {
                    ctx.fillStyle = Math.random() > 0.5 ? varyColor(colors.dirt_dark, 10) : varyColor(colors.dirt_light, 10);
                    ctx.fillRect(Math.random() * T, grassHeightPx + Math.random() * dirtHeightPx, Math.random()*P*1.5+P*0.5, Math.random()*P*1.5+P*0.5);
                }
                addNoise(ctx, T, T, 0.12, ['rgba(0,0,0,0.06)', 'rgba(255,255,255,0.03)'], 0, grassHeightPx, T, dirtHeightPx);

                // Draw grass top part
                ctx.fillStyle = colors.grass_side_top; ctx.fillRect(0, 0, T, grassHeightPx);
                // Draw grass blades hanging down slightly
                for (let i = 0; i < T * 0.8; i++) {
                    const bladeStartX = Math.random() * T;
                    const bladeStartY = grassHeightPx - transitionHeightPx * Math.random() * 0.5; // Start within transition
                    const bladeLength = transitionHeightPx * (1 + Math.random() * 1.2); // Extend downwards
                    const bladeWidth = Math.max(1, P * (0.2 + Math.random() * 0.4));
                    ctx.fillStyle = varyColor(colors.grass_side_top, Math.random() > 0.3 ? -12 : 8); // Vary blade color
                    ctx.fillRect(bladeStartX - bladeWidth/2, bladeStartY, bladeWidth, bladeLength);
                    // Add highlight/shadow to blade
                    ctx.fillStyle = Math.random() > 0.5 ? 'rgba(0,0,0,0.08)' : 'rgba(255,255,255,0.06)';
                    ctx.fillRect(bladeStartX - bladeWidth/2, bladeStartY, bladeWidth * 0.5, bladeLength);
                }
                addNoise(ctx, T, T, 0.08, ['rgba(0,0,0,0.05)', 'rgba(255,255,255,0.04)'], 0, 0, T, grassHeightPx);
            }
            break;
        case BLOCK_TYPE.DIRT:
            // Dirt texture (brown with variations and pebbles)
            ctx.fillStyle = colors.dirt; ctx.fillRect(0, 0, T, T);
            // Add darker/lighter patches
            for (let i = 0; i < T * T * 0.12; i++) {
                ctx.fillStyle = Math.random() > 0.5 ? varyColor(colors.dirt_dark, 12) : varyColor(colors.dirt_light, 12);
                ctx.fillRect(Math.random() * T, Math.random() * T, Math.random()*P*1.8+P*0.8, Math.random()*P*1.8+P*0.8);
            }
            // Add small pebbles
            for (let i = 0; i < T * T * 0.08; i++) {
                ctx.fillStyle = varyColor(colors.dirt_pebble, 5, 0);
                ctx.fillRect(Math.random() * T, Math.random() * T, P*(0.5 + Math.random()*0.5), P*(0.5 + Math.random()*0.5));
            }
            addNoise(ctx, T, T, 0.20); // More noise for dirt
            break;
        case BLOCK_TYPE.STONE:
            // Stone texture (grey variations with cracks)
            ctx.fillStyle = colors.stone_light; ctx.fillRect(0, 0, T, T);
            // Add darker patches
            for (let i = 0; i < T * T * 0.18; i++) {
                ctx.fillStyle = varyColor(colors.stone_dark, 8);
                const x = Math.random() * T; const y = Math.random() * T;
                const size = Math.random()*P*2.0 + P*0.7;
                ctx.fillRect(x, y, size, size);
            }
            // Add mid-tone patches
            for (let i = 0; i < T * T * 0.22; i++) {
                ctx.fillStyle = varyColor(colors.stone, 12);
                const x = Math.random() * T; const y = Math.random() * T;
                const size = Math.random()*P*1.8 + P*0.5;
                ctx.fillRect(x, y, size, size);
            }
            // Add cracks
            ctx.strokeStyle = colors.stone_crack; ctx.lineWidth = Math.max(1, P * 0.2);
            for(let i=0; i < T/10; i++) { // Number of crack segments
                ctx.beginPath();
                const startX = Math.random()*T; const startY = Math.random()*T;
                ctx.moveTo(startX, startY);
                const length = P * (1.5 + Math.random() * 3);
                const angle = Math.random() * Math.PI * 2;
                const endX = startX + Math.cos(angle) * length;
                const endY = startY + Math.sin(angle) * length;
                ctx.lineTo(endX + (Math.random()-0.5)*P*0.8, endY + (Math.random()-0.5)*P*0.8); // Slight jitter
                ctx.stroke();
            }
            addNoise(ctx, T, T, 0.12);
            break;
        case BLOCK_TYPE.WOOD:
            if (face === 'top' || face === 'bottom') {
                // Wood top/bottom (rings)
                ctx.fillStyle = colors.wood_top; ctx.fillRect(0, 0, T, T);
                ctx.strokeStyle = colors.wood_ring;
                const centerX = T / 2 + (Math.random() - 0.5) * P * 1.5; // Offset center slightly
                const centerY = T / 2 + (Math.random() - 0.5) * P * 1.5;
                const maxRadius = T * 0.45;
                let ringStep = Math.max(2, P * (0.8 + Math.random()*0.4) ); // Initial ring distance
                // Draw concentric, slightly irregular rings
                for (let r = ringStep * (0.5 + Math.random()*0.5); r < maxRadius; r += ringStep * (0.7 + Math.random()*0.6)) {
                    ctx.lineWidth = Math.max(1, P * (0.2 + Math.random()*0.6)); // Vary ring thickness
                    ctx.beginPath();
                    const segments = 12; // Smoothness of ring
                    let firstX, firstY;
                    for(let seg=0; seg<=segments; seg++){
                        const angle = (seg/segments) * Math.PI * 2;
                        const radiusX = r * (0.95 + Math.random()*0.1); // Slightly vary radius
                        const radiusY = r * (0.95 + Math.random()*0.1);
                        const angleOffset = (Math.random()-0.5) * 0.1; // Slight angle wobble
                        const x = centerX + Math.cos(angle + angleOffset) * radiusX;
                        const y = centerY + Math.sin(angle + angleOffset) * radiusY;
                        if(seg === 0) { ctx.moveTo(x,y); firstX = x; firstY = y; }
                        else if (seg === segments) { ctx.lineTo(firstX, firstY); } // Close the loop
                        else { ctx.lineTo(x,y); }
                    }
                    ctx.stroke();
                    ringStep = Math.max(2, P * (0.8 + Math.random()*0.4) ); // Vary distance to next ring
                }
                addNoise(ctx, T, T, 0.08);
            } else { // Side face (grain)
                ctx.fillStyle = colors.wood_side; ctx.fillRect(0, 0, T, T);
                ctx.lineWidth = Math.max(1, P * 0.3);
                const grainLines = T/2.5; // Number of main grain lines
                for (let i = 0; i < grainLines; i++) {
                    // Darker grain line
                    ctx.strokeStyle = varyColor(colors.wood_dark, 8, 0.02);
                    ctx.lineWidth = Math.max(1, P * (0.2 + Math.random() * 0.5));
                    ctx.beginPath();
                    let x = (i / grainLines + Math.random() * 0.2 / grainLines) * T; // Slightly randomize start x
                    ctx.moveTo(x + (Math.random()-0.5)*P*0.5, 0);
                    // Draw wiggly line downwards
                    for (let y = P; y <= T; y += P * (1.5 + Math.random())) {
                        ctx.lineTo(x + (Math.random() - 0.5) * P, y); // Horizontal wiggle
                    }
                    ctx.stroke();
                    // Add occasional lighter grain line nearby
                    if (Math.random() > 0.4) {
                        ctx.strokeStyle = varyColor(colors.wood_light_grain, 5, 0.01);
                        ctx.lineWidth = Math.max(1, P * (0.1 + Math.random() * 0.3));
                        ctx.beginPath();
                        let x2 = x + (Math.random()-0.5) * P * 0.8; // Offset from dark line
                        ctx.moveTo(x2 + (Math.random()-0.5)*P*0.3, 0);
                        for (let y = P; y <= T; y += P * (2 + Math.random())) {
                            ctx.lineTo(x2 + (Math.random() - 0.5) * P * 0.8, y);
                        }
                        ctx.stroke();
                    }
                }
                // Add occasional knot
                if(Math.random() < 0.08) {
                    const knotX = Math.random() * T * 0.8 + T*0.1; // Avoid edges
                    const knotY = Math.random() * T * 0.8 + T*0.1;
                    const knotRadius = P * (0.8 + Math.random()*1.2);
                    // Outer knot color
                    ctx.fillStyle = varyColor(colors.wood_dark, -10);
                    ctx.beginPath();
                    ctx.ellipse(knotX, knotY, knotRadius, knotRadius * (0.6 + Math.random()*0.3), Math.random()*Math.PI, 0, Math.PI*2);
                    ctx.fill();
                    // Inner knot color
                    ctx.fillStyle = varyColor(colors.wood_ring, -5);
                    ctx.beginPath();
                    ctx.ellipse(knotX, knotY, knotRadius*0.4, knotRadius * 0.2, Math.random()*Math.PI, 0, Math.PI*2);
                    ctx.fill();
                }
                addNoise(ctx, T, T, 0.08, ['rgba(0,0,0,0.08)', 'rgba(255,255,255,0.03)']);
            }
            break;
        case BLOCK_TYPE.LEAVES:
            // Leaves texture (clusters of green with gaps)
            ctx.fillStyle = colors.leaves; ctx.fillRect(0, 0, T, T);
            const leafCount = T * T * 1.2; // Density of leaf blobs
            // Draw leaf blobs
            for (let i = 0; i < leafCount; i++) {
                let color;
                const randColor = Math.random();
                if (randColor < 0.4) color = varyColor(colors.leaves_light, 8, 0.01);
                else if (randColor < 0.75) color = varyColor(colors.leaves, 8, 0.01);
                else color = varyColor(colors.leaves_dark, 6, 0.01);
                ctx.fillStyle = color;
                const x = Math.random() * T; const y = Math.random() * T;
                const radiusX = Math.random() * (P * 0.8) + (P * 0.3);
                const radiusY = Math.random() * (P * 0.8) + (P * 0.3);
                const angle = Math.random() * Math.PI; // Random orientation
                ctx.beginPath();
                ctx.ellipse(x, y, radiusX, radiusY, angle, 0, Math.PI * 2);
                ctx.fill();
            }
            // Punch holes for transparency
            ctx.globalCompositeOperation = 'destination-out'; // Erase mode
            const gapCount = T * T * 0.06; // Density of gaps
            for (let i = 0; i < gapCount; i++) {
                const x = Math.random() * T; const y = Math.random() * T;
                const radius = Math.random() * (P * 0.5) + (P * 0.2);
                ctx.beginPath();
                ctx.arc(x, y, radius, 0, Math.PI * 2);
                ctx.fill(); // Erase circles
            }
            ctx.globalCompositeOperation = 'source-over'; // Restore default drawing mode
            // Add subtle dark noise/shadowing
            addNoise(ctx, T, T, 0.12, [varyColor(colors.leaves_dark, -10, 0)]);
            break;
        default: // Fallback for unknown types
            ctx.fillStyle = '#FF00FF'; // Bright magenta
            ctx.fillRect(0, 0, T, T);
            ctx.fillStyle = '#000000';
            ctx.font = `${T/4}px sans-serif`; // Adjust font size based on T
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            ctx.fillText('?', T/2, T/2);
            break;
    }

    // Create Three.js texture from canvas
    const texture = new THREE.CanvasTexture(canvas);
    texture.magFilter = THREE.NearestFilter; // Pixelated look when close
    texture.minFilter = THREE.NearestMipmapLinearFilter; // Smoother look when far, uses mipmaps
    texture.colorSpace = THREE.SRGBColorSpace; // Ensure correct color interpretation
    texture.needsUpdate = true; // Important for CanvasTexture

    textureCache[cacheKey] = texture; // Store in cache
    return texture;
}

// --- Material Creation ---
// Creates materials (standard or multi-material array) for each block type
function createProceduralMaterials() {
    // Default PBR properties (adjust for desired look)
    const defaultPBR = { roughness: 0.9, metalness: 0.05 };
    const leavesPBR = { roughness: 0.8, metalness: 0.0 };
    const woodPBR = { roughness: 0.85, metalness: 0.0 };
    const stonePBR = { roughness: 0.75, metalness: 0.1 };

    // Fallback material
    const defaultMaterial = new THREE.MeshStandardMaterial({ color: 0xff00ff, ...defaultPBR, name: "FallbackMaterial" });

    // Loop through all defined block types
    for (const type of Object.values(BLOCK_TYPE)) {
        if (type === BLOCK_TYPE.AIR) continue; // Skip AIR

        const isTransparent = (type === BLOCK_TYPE.LEAVES);
        const needsAlphaTest = isTransparent; // Use alphaTest for sharp transparency cutoff
        let pbrProperties;
        let multiMaterial = false; // Does this block need different textures per face?

        // Assign specific PBR properties and check for multi-material requirement
        switch(type) {
            case BLOCK_TYPE.LEAVES: pbrProperties = leavesPBR; break;
            case BLOCK_TYPE.WOOD:   pbrProperties = woodPBR; multiMaterial = true; break;
            case BLOCK_TYPE.STONE:  pbrProperties = stonePBR; break;
            case BLOCK_TYPE.GRASS:  pbrProperties = defaultPBR; multiMaterial = true; break;
            default:                pbrProperties = defaultPBR; break; // Dirt, etc.
        }

        try {
            if (multiMaterial) {
                // Create an array of materials for [px, nx, py, ny, pz, nz] faces
                const topTexture = generateProceduralTexture(type, 'top');
                // Grass uses 'bottom' texture for bottom face, Wood uses 'top' for both
                const bottomTexture = generateProceduralTexture(type, (type === BLOCK_TYPE.GRASS ? 'bottom' : 'top'));
                const sideTexture = generateProceduralTexture(type, 'side');

                loadedMaterials[type] = [
                    new THREE.MeshStandardMaterial({ map: sideTexture, name: `${BLOCK_NAMES[type]}_px`, ...pbrProperties }), // Right (+x)
                    new THREE.MeshStandardMaterial({ map: sideTexture, name: `${BLOCK_NAMES[type]}_nx`, ...pbrProperties }), // Left (-x)
                    new THREE.MeshStandardMaterial({ map: topTexture, name: `${BLOCK_NAMES[type]}_py`, ...pbrProperties }),  // Top (+y)
                    new THREE.MeshStandardMaterial({ map: bottomTexture, name: `${BLOCK_NAMES[type]}_ny`, ...pbrProperties }),// Bottom (-y)
                    new THREE.MeshStandardMaterial({ map: sideTexture, name: `${BLOCK_NAMES[type]}_pz`, ...pbrProperties }), // Front (+z)
                    new THREE.MeshStandardMaterial({ map: sideTexture, name: `${BLOCK_NAMES[type]}_nz`, ...pbrProperties })  // Back (-z)
                ];
                // Ensure materials update if textures were newly generated
                loadedMaterials[type].forEach(mat => mat.needsUpdate = true);
            } else {
                // Create a single material for all faces
                const texture = generateProceduralTexture(type, 'side'); // Use 'side' texture for all faces
                loadedMaterials[type] = new THREE.MeshStandardMaterial({
                    map: texture,
                    transparent: isTransparent,
                    alphaTest: needsAlphaTest ? 0.1 : 0, // Discard pixels with alpha < 0.1
                    side: isTransparent ? THREE.DoubleSide : THREE.FrontSide, // Render both sides for leaves
                    name: `${BLOCK_NAMES[type]}`,
                    ...pbrProperties
                });
                loadedMaterials[type].needsUpdate = true;
            }
        } catch (error) {
            console.error(`Failed to create material for block type ${type} (${BLOCK_NAMES[type]}):`, error);
            loadedMaterials[type] = defaultMaterial; // Use fallback on error
        }
    }

    // Final check to ensure all non-AIR types have a material assigned
    for (const type of Object.values(BLOCK_TYPE)) {
        if (type !== BLOCK_TYPE.AIR && !loadedMaterials[type]) {
            console.warn(`Missing material for block type ${type} (${BLOCK_NAMES[type]}). Using fallback.`);
            loadedMaterials[type] = defaultMaterial;
        }
    }
}

// --- Create Torch ---
// Builds the torch model (handle, flame), light source, and particle system, attaching it to the camera
function createTorch() {
    torchMesh = new THREE.Group();
    torchMesh.name = "TorchViewModel";

    // Handle Material (try to use generated wood, fallback to brown)
    let handleMaterial = loadedMaterials[BLOCK_TYPE.WOOD];
    if (!handleMaterial || !Array.isArray(handleMaterial)) { // Check if wood material exists and is the expected array
        console.warn("Wood material for torch handle not found or invalid! Using fallback color.");
        handleMaterial = new THREE.MeshStandardMaterial({ color: 0x8B4513, roughness: 0.8 });
    } else {
        handleMaterial = handleMaterial[0]; // Use the side material from the wood array
    }

    // Flame Material (additive blending for glow effect)
    const flameMaterial = new THREE.MeshBasicMaterial({
        color: 0xFFA500, // Orange
        blending: THREE.AdditiveBlending,
        transparent: true,
        opacity: 0.85,
        side: THREE.DoubleSide,
        depthWrite: false // Don't obscure things behind it
    });

    // Geometry sizes
    const handleHeight = 0.5;
    const handleRadius = 0.04;
    const flameRadius = 0.05;

    // Handle Mesh
    const handleGeo = new THREE.CylinderGeometry(handleRadius, handleRadius * 0.8, handleHeight, 8);
    const handleMesh = new THREE.Mesh(handleGeo, handleMaterial);
    handleMesh.position.y = -handleHeight * 0.4; // Position handle slightly lower
    torchMesh.add(handleMesh);

    // Flame Mesh (simple sphere)
    const flameGeo = new THREE.SphereGeometry(flameRadius, 8, 6);
    flameMesh = new THREE.Mesh(flameGeo, flameMaterial);
    const flameBaseY = handleMesh.position.y + handleHeight / 2 + flameRadius * 0.1; // Position flame just above handle top
    flameMesh.position.y = flameBaseY + flameRadius * 0.5; // Center flame slightly higher
    torchMesh.add(flameMesh);

    // Point Light source emanating from the flame
    torchLight = new THREE.PointLight(0xffaa33, torchBaseLightIntensity, 7, 2); // Color, Intensity, Distance, Decay
    torchLight.position.copy(flameMesh.position); // Position light at flame center
    torchLight.castShadow = false; // Viewmodel light shouldn't cast shadows generally
    torchMesh.add(torchLight);

    // --- Particle System ---
    particleGeometry = new THREE.BufferGeometry();
    particlePositions = new Float32Array(particleCount * 3); // x, y, z for each particle
    particleVelocities = []; // Store Vector3 velocities
    particleLifetimes = new Float32Array(particleCount); // Store remaining lifetime

    const flameOrigin = new THREE.Vector3(0, flameBaseY, 0); // Base spawn point for particles

    // Initialize particles
    for (let i = 0; i < particleCount; i++) {
        const i3 = i * 3;
        // Start position near flame base, slightly randomized
        particlePositions[i3] = flameOrigin.x + (Math.random() - 0.5) * particleSpawnRadius * 2;
        particlePositions[i3 + 1] = flameOrigin.y + Math.random() * 0.05;
        particlePositions[i3 + 2] = flameOrigin.z + (Math.random() - 0.5) * particleSpawnRadius * 2;

        // Initial velocity (mostly upwards, slight sideways variance)
        const vel = new THREE.Vector3(
            (Math.random() - 0.5) * particleVelocityVariance * 0.5,
            particleBaseVelocityY + Math.random() * particleVelocityVariance,
            (Math.random() - 0.5) * particleVelocityVariance * 0.5
        );
        particleVelocities.push(vel);

        // Initial lifetime (base + random variance)
        particleLifetimes[i] = particleBaseLifetime + (Math.random() - 0.5) * particleLifetimeVariance * 2;
    }

    // Set geometry attributes
    particleGeometry.setAttribute('position', new THREE.BufferAttribute(particlePositions, 3));

    // Particle Material
    particleMaterial = new THREE.PointsMaterial({
        color: 0xffcc66, // Lighter orange/yellow
        size: 0.015,
        blending: THREE.AdditiveBlending,
        transparent: true,
        depthWrite: false,
        sizeAttenuation: true // Particles get smaller further away
    });

    // Create Points object
    particleSystem = new THREE.Points(particleGeometry, particleMaterial);
    particleSystem.name = "TorchParticles";
    torchMesh.add(particleSystem);

    // --- Final Torch Positioning and Attachment ---
    // Position the torch group relative to the camera (viewmodel position)
    torchMesh.position.set(0.30, -0.25, -0.45); // Right, Down, Forward
    torchMesh.rotation.set(0, -Math.PI / 16, Math.PI / 14); // Slight tilt

    // Add the entire torch group to the camera
    camera.add(torchMesh);
}


// --- World & Chunk Management ---
// Get chunk coordinates (cx, cz) from world coordinates (wx, wz)
function getChunkCoords(worldX, worldZ) {
    return {
        x: Math.floor(worldX / CHUNK_SIZE_X),
        z: Math.floor(worldZ / CHUNK_SIZE_Z)
    };
}
// Get a unique string key for a chunk
function getChunkKey(chunkX, chunkZ) {
    return `${chunkX},${chunkZ}`;
}
// Get the block type at specific world coordinates
function getBlockWorld(worldX, worldY, worldZ) {
    const { x: chunkX, z: chunkZ } = getChunkCoords(worldX, worldZ);
    const key = getChunkKey(chunkX, chunkZ);
    const chunkData = worldChunks.get(key);

    // Check if chunk exists and coordinates are within vertical bounds
    if (!chunkData || worldY < 0 || worldY >= CHUNK_SIZE_Y) {
        return BLOCK_TYPE.AIR; // Outside loaded world or height limits is AIR
    }

    // Calculate local coordinates within the chunk
    const localX = THREE.MathUtils.euclideanModulo(Math.floor(worldX), CHUNK_SIZE_X);
    const localZ = THREE.MathUtils.euclideanModulo(Math.floor(worldZ), CHUNK_SIZE_Z);
    const localY = Math.floor(worldY);

    // Access block data (handle potential sparse arrays)
    return chunkData[localX]?.[localZ]?.[localY] ?? BLOCK_TYPE.AIR;
}
// Set the block type at specific world coordinates
function setBlockWorld(worldX, worldY, worldZ, blockType) {
    const { x: chunkX, z: chunkZ } = getChunkCoords(worldX, worldZ);
    const key = getChunkKey(chunkX, chunkZ);
    let chunkData = worldChunks.get(key);

    // Check if chunk exists and coordinates are valid
    if (!chunkData || worldY < 0 || worldY >= CHUNK_SIZE_Y) {
        return; // Cannot modify unloaded or out-of-bounds blocks
    }

    // Calculate local coordinates
    const localX = THREE.MathUtils.euclideanModulo(Math.floor(worldX), CHUNK_SIZE_X);
    const localZ = THREE.MathUtils.euclideanModulo(Math.floor(worldZ), CHUNK_SIZE_Z);
    const localY = Math.floor(worldY);

    // Ensure nested arrays exist (might be sparse initially)
    if (!chunkData[localX]) chunkData[localX] = [];
    if (!chunkData[localX][localZ]) chunkData[localX][localZ] = new Uint8Array(CHUNK_SIZE_Y).fill(BLOCK_TYPE.AIR);

    // Only update if the block type actually changes
    if (chunkData[localX][localZ][localY] !== blockType) {
        chunkData[localX][localZ][localY] = blockType;

        // Regenerate the mesh for the modified chunk
        disposeChunkMesh(chunkX, chunkZ);
        createChunkMesh(chunkX, chunkZ);

        // Check if the modification happened at a chunk border and update neighbors
        const neighborsToUpdate = [];
        if (localX === 0)                  neighborsToUpdate.push({ x: chunkX - 1, z: chunkZ });
        else if (localX === CHUNK_SIZE_X - 1) neighborsToUpdate.push({ x: chunkX + 1, z: chunkZ });
        if (localZ === 0)                  neighborsToUpdate.push({ x: chunkX, z: chunkZ - 1 });
        else if (localZ === CHUNK_SIZE_Z - 1) neighborsToUpdate.push({ x: chunkX, z: chunkZ + 1 });
        // No need to check Y borders for mesh updates in this system

        // Regenerate meshes for affected neighbors if they are currently loaded
        neighborsToUpdate.forEach(n => {
            const neighborKey = getChunkKey(n.x, n.z);
            if (chunkMeshes.has(neighborKey)) { // Only update if neighbor mesh exists
                disposeChunkMesh(n.x, n.z);
                createChunkMesh(n.x, n.z);
            }
        });
    }
}
// Generate terrain data for a chunk using noise
function generateChunkData(chunkX, chunkZ) {
    // Initialize chunk data array [x][z][y]
    const chunkData = Array(CHUNK_SIZE_X).fill(0).map(() =>
        Array(CHUNK_SIZE_Z).fill(0).map(() =>
            new Uint8Array(CHUNK_SIZE_Y).fill(BLOCK_TYPE.AIR)
        )
    );

    const baseHeight = Math.floor(WORLD_HEIGHT * 0.3); // Base ground level

    for (let lx = 0; lx < CHUNK_SIZE_X; lx++) {
        for (let lz = 0; lz < CHUNK_SIZE_Z; lz++) {
            const worldX = chunkX * CHUNK_SIZE_X + lx;
            const worldZ = chunkZ * CHUNK_SIZE_Z + lz;

            // Calculate terrain height using octave noise
            const noiseVal = octaveNoise(worldX, worldZ, 5, 0.5, 2.0, 0.012); // Parameters control terrain shape
            const terrainHeight = baseHeight + Math.floor(noiseVal * WORLD_HEIGHT * 0.25); // Apply noise to base height

            // Determine stone depth
            const stoneHeight = terrainHeight - (3 + Math.floor(Math.random() * 3)); // 3-5 blocks of soil/grass on top

            // Fill blocks from bottom up
            for (let ly = 0; ly < CHUNK_SIZE_Y; ly++) {
                if (ly < stoneHeight) {
                    chunkData[lx][lz][ly] = BLOCK_TYPE.STONE;
                } else if (ly < terrainHeight - 1) {
                    chunkData[lx][lz][ly] = BLOCK_TYPE.DIRT;
                } else if (ly < terrainHeight) {
                    chunkData[lx][lz][ly] = BLOCK_TYPE.GRASS;
                } // Above terrainHeight remains AIR
            }

            // --- Simple Tree Generation ---
            // Only place trees on grass blocks, with a low probability
            if (chunkData[lx][lz][terrainHeight - 1] === BLOCK_TYPE.GRASS && Math.random() < 0.015) { // ~1.5% chance per grass block
                const treeHeight = Math.floor(Math.random() * 4) + 4; // 4-7 blocks tall trunk

                // Create trunk
                for(let h=0; h<treeHeight; h++) {
                    if(terrainHeight + h < CHUNK_SIZE_Y) { // Check vertical bounds
                        chunkData[lx][lz][terrainHeight + h] = BLOCK_TYPE.WOOD;
                    }
                }

                // Create leaves (simple sphere/cube shape)
                const leafRadius = 2.5;
                const leafRadiusInt = Math.ceil(leafRadius);
                const leafCenterY = terrainHeight + treeHeight - 1; // Center leaves around top of trunk

                for (let dy = -leafRadiusInt; dy <= leafRadiusInt; dy++) {
                    for (let dx = -leafRadiusInt; dx <= leafRadiusInt; dx++) {
                        for (let dz = -leafRadiusInt; dz <= leafRadiusInt; dz++) {
                            // Check distance for spherical shape
                            const distSq = dx*dx + dy*dy + dz*dz;
                            if (distSq > leafRadius * leafRadius) continue; // Skip if outside radius

                            const targetX = lx + dx;
                            const targetY = leafCenterY + dy;
                            const targetZ = lz + dz;

                            // Check if target coordinates are within the *current chunk's bounds*
                            if (targetX >= 0 && targetX < CHUNK_SIZE_X &&
                                targetY >= 0 && targetY < CHUNK_SIZE_Y &&
                                targetZ >= 0 && targetZ < CHUNK_SIZE_Z)
                            {
                                const finalTargetY = Math.floor(targetY);
                                // Only place leaves if the spot is currently AIR (don't overwrite trunk/other leaves)
                                if (chunkData[targetX]?.[targetZ]?.[finalTargetY] === BLOCK_TYPE.AIR) {
                                     // Check nested arrays exist before access
                                     if (!chunkData[targetX]) chunkData[targetX] = [];
                                     if (!chunkData[targetX][targetZ]) chunkData[targetX][targetZ] = new Uint8Array(CHUNK_SIZE_Y).fill(BLOCK_TYPE.AIR);
                                     chunkData[targetX][targetZ][finalTargetY] = BLOCK_TYPE.LEAVES;
                                }
                            }
                            // Note: This simple tree generation doesn't handle leaves crossing chunk boundaries perfectly.
                        }
                    }
                }
            } // End tree generation
        }
    }
    return chunkData;
}

// Shared geometry for all block instances (performance boost)
const sharedBoxGeometry = new THREE.BoxGeometry(1, 1, 1);

// Creates an InstancedMesh for each block type present in a chunk
function createChunkMesh(chunkX, chunkZ) {
    const key = getChunkKey(chunkX, chunkZ);
    let chunkData = worldChunks.get(key);

    // Generate data if it doesn't exist
    if (!chunkData) {
        chunkData = generateChunkData(chunkX, chunkZ);
        worldChunks.set(key, chunkData);
    }

    // Ensure any old mesh for this chunk is removed first
    disposeChunkMesh(chunkX, chunkZ);

    // Chunk world origin
    const chunkOriginX = chunkX * CHUNK_SIZE_X;
    const chunkOriginZ = chunkZ * CHUNK_SIZE_Z;

    // Use a temporary matrix for setting instance positions
    const matrix = new THREE.Matrix4();
    // Store matrices for each block type { typeId: [matrix1, matrix2, ...] }
    const instances = {};

    // Iterate through all blocks in the chunk
    for (let lx = 0; lx < CHUNK_SIZE_X; lx++) {
        for (let lz = 0; lz < CHUNK_SIZE_Z; lz++) {
            if (!chunkData[lx]?.[lz]) continue; // Skip if column is empty
            for (let ly = 0; ly < CHUNK_SIZE_Y; ly++) {
                const blockType = chunkData[lx][lz][ly];
                if (blockType === BLOCK_TYPE.AIR) continue; // Skip air blocks

                const worldX = chunkOriginX + lx;
                const worldY = ly;
                const worldZ = chunkOriginZ + lz;

                // --- Culling Check ---
                // Check neighbors: if any neighbor is transparent or air, this block face is visible
                const isExposed =
                    isTransparentOrAir(getBlockWorld(worldX + 1, worldY, worldZ)) || // Right
                    isTransparentOrAir(getBlockWorld(worldX - 1, worldY, worldZ)) || // Left
                    isTransparentOrAir(getBlockWorld(worldX, worldY + 1, worldZ)) || // Top
                    isTransparentOrAir(getBlockWorld(worldX, worldY - 1, worldZ)) || // Bottom
                    isTransparentOrAir(getBlockWorld(worldX, worldY, worldZ + 1)) || // Front
                    isTransparentOrAir(getBlockWorld(worldX, worldY, worldZ - 1));   // Back

                if (isExposed) {
                    // Initialize array for this type if first instance found
                    if (!instances[blockType]) instances[blockType] = [];

                    // Set matrix position (center of the block)
                    matrix.setPosition(worldX + 0.5, worldY + 0.5, worldZ + 0.5);
                    // Add a clone of the matrix to the list for this block type
                    instances[blockType].push(matrix.clone());
                }
            }
        }
    }

    // Create InstancedMeshes from the collected matrices
    const chunkMeshGroup = {}; // To store the meshes created for this chunk
    for (const typeStr in instances) {
        const type = parseInt(typeStr);
        const instanceMatrices = instances[type];
        const count = instanceMatrices.length;
        if (count === 0) continue; // Skip if no instances of this type

        const material = loadedMaterials[type];
        if (!material) {
            console.warn(`Material not found for type ${type} in chunk ${key}, skipping mesh.`);
            continue;
        }

        // Create InstancedMesh (geometry, material, count)
        const mesh = new THREE.InstancedMesh(sharedBoxGeometry, material, count);
        mesh.name = `chunk_${key}_type_${type}`;
        mesh.castShadow = true;
        mesh.receiveShadow = true;
        mesh.userData.chunkKey = key; // Store key for later identification

        // Apply the transformation matrices to each instance
        for (let i = 0; i < count; i++) {
            mesh.setMatrixAt(i, instanceMatrices[i]);
        }
        mesh.instanceMatrix.needsUpdate = true; // Crucial after setting matrices

        scene.add(mesh); // Add mesh to the scene
        chunkMeshGroup[type] = mesh; // Store reference to this mesh
    }

    // Store the group of meshes associated with this chunk key
    if (Object.keys(chunkMeshGroup).length > 0) {
        chunkMeshes.set(key, chunkMeshGroup);
    } else {
        // If chunk ended up being empty (e.g., all air), remove potential old entry
        chunkMeshes.delete(key);
    }
}
// Remove and dispose of all meshes associated with a chunk
function disposeChunkMesh(chunkX, chunkZ) {
    const key = getChunkKey(chunkX, chunkZ);
    const meshGroup = chunkMeshes.get(key);
    if (meshGroup) {
        // Remove each InstancedMesh within the group from the scene
        for (const type in meshGroup) {
            scene.remove(meshGroup[type]);
            // Note: Geometry and Material are shared, so don't dispose them here.
            // InstancedMesh disposal is handled by removing it from the scene.
        }
        chunkMeshes.delete(key); // Remove the entry from the map
    }
}
// Helper to check if a block type allows light/vision through
function isTransparentOrAir(blockType) {
    return blockType === BLOCK_TYPE.AIR || blockType === BLOCK_TYPE.LEAVES;
}
// Check which chunks should be visible based on player position and RENDER_DISTANCE
function updateVisibleChunks(forceLoad = false) {
    // Need controls and camera to be ready
    if (!controls || !camera) return;

    const camPos = controls.getObject().position;
    const { x: currentChunkX, z: currentChunkZ } = getChunkCoords(camPos.x, camPos.z);

    // If player hasn't moved to a new chunk and not forced, do nothing
    if (!forceLoad && currentChunkX === player.currentChunk.x && currentChunkZ === player.currentChunk.z) {
        return;
    }

    const chunkChanged = player.currentChunk.x !== currentChunkX || player.currentChunk.z !== currentChunkZ;
    player.currentChunk = { x: currentChunkX, z: currentChunkZ }; // Update player's current chunk

    // Update light target when chunk changes to keep shadows centered
    if (chunkChanged) {
        updateLightTarget();
    }

    const chunksToKeep = new Set(); // Chunks that should remain loaded
    const chunksToLoad = []; // Chunks that need to be loaded/generated

    // Iterate in a square grid around the player's chunk
    for (let dx = -RENDER_DISTANCE; dx <= RENDER_DISTANCE; dx++) {
        for (let dz = -RENDER_DISTANCE; dz <= RENDER_DISTANCE; dz++) {
            // Optional: Use circular distance check for slightly better performance/look
            if (dx * dx + dz * dz > RENDER_DISTANCE * RENDER_DISTANCE) continue;

            const chunkX = currentChunkX + dx;
            const chunkZ = currentChunkZ + dz;
            const key = getChunkKey(chunkX, chunkZ);

            chunksToKeep.add(key); // Mark this chunk as needed

            // If this chunk doesn't have a mesh yet, add it to the load list
            if (!chunkMeshes.has(key)) {
                chunksToLoad.push({ x: chunkX, z: chunkZ });
            }
        }
    }

    // --- Unload distant chunks ---
    for (const key of chunkMeshes.keys()) {
        if (!chunksToKeep.has(key)) {
            // This chunk mesh is loaded but no longer in render distance
            const [cxStr, czStr] = key.split(',');
            disposeChunkMesh(parseInt(cxStr), parseInt(czStr));
            // Optional: Also remove chunk *data* from worldChunks map to save memory
            // worldChunks.delete(key); // Uncomment if memory is a concern
        }
    }

    // --- Load new chunks ---
    // Sort chunks to load by distance? (Optional optimization)
    // chunksToLoad.sort((a, b) => ...);

    // Create meshes for chunks that entered the render distance
    chunksToLoad.forEach(coords => {
        // Double-check it wasn't loaded somehow between checks (unlikely but safe)
        if (!chunkMeshes.has(getChunkKey(coords.x, coords.z))) {
            createChunkMesh(coords.x, coords.z);
        }
    });
}


// --- Collision & Interaction ---
// Checks for collision between the player's bounding box and solid blocks
function checkCollision(position, checkGround = false) {
    // Define player's bounding box based on proposed position
    const groundCheckOffset = checkGround ? 0.1 : 0; // Check slightly below feet for ground check
    const playerBox = new THREE.Box3(
        new THREE.Vector3(position.x - player.radius, position.y - player.height - groundCheckOffset, position.z - player.radius), // Bottom back left
        new THREE.Vector3(position.x + player.radius, position.y, position.z + player.radius)  // Top front right
    );

    // Get the range of world block coordinates the player box could overlap with
    const minX = Math.floor(playerBox.min.x);
    const maxX = Math.ceil(playerBox.max.x);
    const minY = Math.floor(playerBox.min.y);
    const maxY = Math.ceil(playerBox.max.y);
    const minZ = Math.floor(playerBox.min.z);
    const maxZ = Math.ceil(playerBox.max.z);

    // Iterate through potentially colliding blocks
    for (let worldX = minX; worldX < maxX; worldX++) {
        for (let worldY = minY; worldY < maxY; worldY++) {
            for (let worldZ = minZ; worldZ < maxZ; worldZ++) {
                const blockType = getBlockWorld(worldX, worldY, worldZ);
                // Check if the block is solid
                if (isSolid(blockType)) {
                    // Create bounding box for the solid block
                    const blockBox = new THREE.Box3(
                        new THREE.Vector3(worldX, worldY, worldZ),
                        new THREE.Vector3(worldX + 1, worldY + 1, worldZ + 1)
                    );
                    // Check for intersection
                    if (playerBox.intersectsBox(blockBox)) {
                        return true; // Collision detected
                    }
                }
            }
        }
    }
    return false; // No collision found
}
// Helper to check if a block type is solid (collidable)
function isSolid(blockType) {
    // Define which block types player should collide with
    return blockType !== BLOCK_TYPE.AIR && blockType !== BLOCK_TYPE.LEAVES; // Extend this if adding water, etc.
}
// Handles mouse clicks for breaking/placing blocks
function handleBlockInteraction(event) {
    // Only interact if pointer is locked
    if (!controls || !controls.isLocked) return;
    // Left click = 0, Middle = 1, Right click = 2
    raycastAndInteract(event.button);
}
// Perform voxel raycast and interact based on mouse button
function raycastAndInteract(button) {
    // Ray starts at camera position, direction is where camera is looking
    raycaster.setFromCamera({ x: 0, y: 0 }, camera); // Use center of screen
    const direction = raycaster.ray.direction;
    const origin = raycaster.ray.origin;

    // Voxel traversal algorithm (Amanatides & Woo)
    let currentX = Math.floor(origin.x);
    let currentY = Math.floor(origin.y);
    let currentZ = Math.floor(origin.z);

    const stepX = Math.sign(direction.x);
    const stepY = Math.sign(direction.y);
    const stepZ = Math.sign(direction.z);

    // Calculate distance to nearest voxel boundary in each direction
    const nextVoxelX = currentX + (stepX > 0 ? 1 : 0);
    const nextVoxelY = currentY + (stepY > 0 ? 1 : 0);
    const nextVoxelZ = currentZ + (stepZ > 0 ? 1 : 0);

    // Calculate t needed to travel to the next boundary
    let tMaxX = (direction.x === 0) ? Infinity : (nextVoxelX - origin.x) / direction.x;
    let tMaxY = (direction.y === 0) ? Infinity : (nextVoxelY - origin.y) / direction.y;
    let tMaxZ = (direction.z === 0) ? Infinity : (nextVoxelZ - origin.z) / direction.z;

    // Calculate t needed to travel 1 unit in each direction
    const tDeltaX = (direction.x === 0) ? Infinity : Math.abs(1 / direction.x);
    const tDeltaY = (direction.y === 0) ? Infinity : Math.abs(1 / direction.y);
    const tDeltaZ = (direction.z === 0) ? Infinity : Math.abs(1 / direction.z);

    let hitBlockCoords = null; // Coordinates of the block hit
    let prevBlockCoords = null; // Coordinates of the block *before* the hit (for placing)
    let dist = 0; // Distance traveled along the ray

    // Step through voxels along the ray
    for (let i = 0; i < MAX_RAYCAST_DISTANCE * 2 ; i++) { // Limit steps to avoid infinite loops
        const blockType = getBlockWorld(currentX, currentY, currentZ);

        // Check if the current voxel is solid
        if (isSolid(blockType)) {
            hitBlockCoords = { x: currentX, y: currentY, z: currentZ };
            break; // Found a solid block, stop traversal
        }

        // Store the last air block coordinates before potentially hitting a solid one
        prevBlockCoords = { x: currentX, y: currentY, z: currentZ };

        // Determine which direction to step next (the one with the smallest tMax)
        let tStep;
        if (tMaxX < tMaxY) {
            if (tMaxX < tMaxZ) {
                tStep = tMaxX; // Step in X
                currentX += stepX;
                tMaxX += tDeltaX;
            } else {
                tStep = tMaxZ; // Step in Z
                currentZ += stepZ;
                tMaxZ += tDeltaZ;
            }
        } else {
            if (tMaxY < tMaxZ) {
                tStep = tMaxY; // Step in Y
                currentY += stepY;
                tMaxY += tDeltaY;
            } else {
                tStep = tMaxZ; // Step in Z
                currentZ += stepZ;
                tMaxZ += tDeltaZ;
            }
        }

        dist = tStep; // Update distance traveled
        // Stop if ray goes beyond max distance
        if (dist > MAX_RAYCAST_DISTANCE) break;
    }

    // --- Perform Action based on button and raycast result ---
    if (button === 0 && hitBlockCoords) { // Left Click: Break block
        setBlockWorld(hitBlockCoords.x, hitBlockCoords.y, hitBlockCoords.z, BLOCK_TYPE.AIR);
    } else if (button === 2 && hitBlockCoords && prevBlockCoords) { // Right Click: Place block
        // --- Placement Collision Check ---
        // Prevent placing block inside the player
        const playerEyePos = player.position; // Camera position is eye level
        const playerFeetY = playerEyePos.y - player.height;
        const playerHeadY = playerEyePos.y;
        const playerMinX = playerEyePos.x - player.radius;
        const playerMaxX = playerEyePos.x + player.radius;
        const playerMinZ = playerEyePos.z - player.radius;
        const playerMaxZ = playerEyePos.z + player.radius;

        const placeX = prevBlockCoords.x;
        const placeY = prevBlockCoords.y;
        const placeZ = prevBlockCoords.z;

        // Check if player's bounding box overlaps with the placement coordinates
        const intersectsX = playerMaxX > placeX && playerMinX < placeX + 1;
        const intersectsZ = playerMaxZ > placeZ && playerMinZ < placeZ + 1;
        const intersectsY = playerHeadY > placeY && playerFeetY < placeY + 1; // Check full height

        if (!(intersectsX && intersectsY && intersectsZ)) {
            // Place the block if no collision with player
            setBlockWorld(prevBlockCoords.x, prevBlockCoords.y, prevBlockCoords.z, blockToPlace);
        } else {
            // console.log("Cannot place block inside player."); // Optional feedback
        }
    }
}


// --- Event Handlers ---
function onWindowResize() {
    if (!camera || !renderer) return; // Check if initialized
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
}
function onKeyDown(event) {
    switch (event.code) {
        // Movement
        case 'KeyW': moveForward = true; break;
        case 'KeyA': moveLeft = true; break;
        case 'KeyS': moveBackward = true; break;
        case 'KeyD': moveRight = true; break;
        // Vertical / Jump / Crouch
        case 'Space': moveUp = true; break;
        case 'ShiftLeft': case 'ShiftRight': moveDown = true; break;
        // Toggles
        case 'KeyF':
            player.flyMode = !player.flyMode;
            player.velocity.y = 0; // Prevent residual jump/fall velocity when toggling
            console.log("Fly mode:", player.flyMode);
            break;
        // Block Selection
        case 'Digit1': blockToPlace = BLOCK_TYPE.STONE; break;
        case 'Digit2': blockToPlace = BLOCK_TYPE.DIRT; break;
        case 'Digit3': blockToPlace = BLOCK_TYPE.GRASS; break;
        case 'Digit4': blockToPlace = BLOCK_TYPE.WOOD; break;
        case 'Digit5': blockToPlace = BLOCK_TYPE.LEAVES; break;
    }
    // Update block info display if a digit key was pressed
    if (event.code.startsWith('Digit') && blockInfoDiv) {
        blockInfoDiv.textContent = `Placing: ${BLOCK_NAMES[blockToPlace]}`;
    }
}
function onKeyUp(event) {
    switch (event.code) {
        case 'KeyW': moveForward = false; break;
        case 'KeyA': moveLeft = false; break;
        case 'KeyS': moveBackward = false; break;
        case 'KeyD': moveRight = false; break;
        case 'Space': moveUp = false; break;
        case 'ShiftLeft': case 'ShiftRight': moveDown = false; break;
    }
}
function onMouseDown(event) {
    // Forward click event to interaction handler
    handleBlockInteraction(event);
}

// --- Light Target Update ---
// Centers the directional light target on the player's current chunk area
function updateLightTarget() {
    if (sunLight && moonLight && player.currentChunk.x !== null) {
        // Target the center of the player's current chunk
        const targetX = player.currentChunk.x * CHUNK_SIZE_X + CHUNK_SIZE_X / 2;
        const targetZ = player.currentChunk.z * CHUNK_SIZE_Z + CHUNK_SIZE_Z / 2;
        // Setting y=0 works fine for directional lights
        sunLight.target.position.set(targetX, 0, targetZ);
        moonLight.target.position.set(targetX, 0, targetZ);
        // Important: Update the target's world matrix so the light knows where to point
        sunLight.target.updateMatrixWorld();
        moonLight.target.updateMatrixWorld();
    }
}

// --- Atmosphere Update ---
// Updates sky color, fog, light intensity/color based on gameTime
const tempColor = new THREE.Color(); // Reusable color object for lerping
function updateAtmosphere(delta) {
    // Increment game time (cycles 0.0 to 1.0)
    gameTime += delta / DAY_CYCLE_SECONDS;
    gameTime %= 1.0; // Wrap around at 1.0

    // Calculate sun/moon positions based on time
    const sunAngle = gameTime * Math.PI * 2; // Full circle over the cycle
    // Distance should be large enough to seem infinitely far
    const sunDistance = RENDER_DISTANCE * CHUNK_SIZE_X * 0.8; // Relative to render distance
    const sunX = Math.cos(sunAngle) * sunDistance; // Horizontal position (East/West)
    const sunY = Math.sin(sunAngle) * sunDistance; // Vertical position (Altitude)
    const sunZ = 0; // Keep sun/moon on a simple North/South plane for simplicity

    // Update light positions relative to the *target* position
    const targetPos = sunLight.target.position; // Assumes target is updated elsewhere (updateLightTarget)
    sunLight.position.set(targetPos.x + sunX, targetPos.y + sunY + 50, targetPos.z + sunZ); // Add offset to target
    moonLight.position.set(targetPos.x - sunX, targetPos.y - sunY + 50, targetPos.z - sunZ); // Opposite side

    // Update visual meshes
    if (sunMesh) sunMesh.position.copy(sunLight.position);
    if (moonMesh) moonMesh.position.copy(moonLight.position);

    // --- Time-based Color and Intensity Calculation ---
    const dawnTime = 0.22, dayTime = 0.28, duskTime = 0.72, nightTime = 0.78;
    const transitionDuration = dayTime - dawnTime; // Assumes dawn/dusk transitions are same length

    let skyColor, groundColor, sunColor;
    let sunIntensity = 0, moonIntensity = 0, hemiIntensity = 0, starsOpacity = 0;

    if (gameTime >= dawnTime && gameTime < dayTime) { // Dawn Transition
        const t = (gameTime - dawnTime) / transitionDuration; // Interpolation factor (0 to 1)
        skyColor = tempColor.copy(skyColors.dawn).lerp(skyColors.day, t);
        groundColor = tempColor.copy(groundColors.dawn).lerp(groundColors.day, t);
        sunColor = tempColor.copy(sunLightColors.dawn).lerp(sunLightColors.day, t);
        sunIntensity = lerp(0.5, 1.8, t); // Sun fades in
        hemiIntensity = lerp(0.4, 1.0, t); // Ambient fades in
        starsOpacity = lerp(0.8, 0, t); // Stars fade out
    } else if (gameTime >= dayTime && gameTime < duskTime) { // Daytime
        skyColor = skyColors.day;
        groundColor = groundColors.day;
        sunColor = sunLightColors.day;
        // Make sun slightly brighter near noon (0.5)
        const noonFactor = 1.0 - Math.abs(gameTime - 0.5) / (duskTime - 0.5); // 1.0 at noon, 0.0 at dusk/day start
        sunIntensity = lerp(1.0, 1.8, noonFactor); // Adjust max intensity here
        hemiIntensity = 1.0;
        starsOpacity = 0;
    } else if (gameTime >= duskTime && gameTime < nightTime) { // Dusk Transition
        const t = (gameTime - duskTime) / transitionDuration;
        skyColor = tempColor.copy(skyColors.dusk).lerp(skyColors.night, t);
        groundColor = tempColor.copy(groundColors.dusk).lerp(groundColors.night, t);
        sunColor = tempColor.copy(sunLightColors.dusk).lerp(sunLightColors.night, t);
        sunIntensity = lerp(1.0, 0.0, t); // Sun fades out
        moonIntensity = lerp(0.0, 0.15, t); // Moon fades in
        hemiIntensity = lerp(1.0, 0.2, t); // Ambient fades out
        starsOpacity = lerp(0, 0.9, t); // Stars fade in
    } else { // Nighttime (covers wrap-around from < dawnTime)
        skyColor = skyColors.night;
        groundColor = groundColors.night;
        sunColor = sunLightColors.night; // Effectively black
        sunIntensity = 0.0;
        moonIntensity = 0.15; // Constant moon intensity at night
        hemiIntensity = 0.2; // Low ambient light
        starsOpacity = 0.9; // Max stars opacity
    }

    // Apply calculated values
    if (scene) {
        scene.background = skyColor;
        if (scene.fog) {
            scene.fog.color.copy(skyColor);
            // Adjust fog density based on light level (denser at night/transitions)
            const fogNearFactor = hemiIntensity < 0.5 ? 0.3 : 0.4;
            const fogFarFactor = hemiIntensity < 0.5 ? 0.9 : 1.0;
            scene.fog.near = RENDER_DISTANCE * CHUNK_SIZE_X * fogNearFactor;
            scene.fog.far = RENDER_DISTANCE * CHUNK_SIZE_X * fogFarFactor;
        }
    }
    if (hemisphereLight) {
        hemisphereLight.color.copy(skyColor);
        hemisphereLight.groundColor.copy(groundColor);
        hemisphereLight.intensity = hemiIntensity;
    }
    if (sunLight) {
        sunLight.color.copy(sunColor);
        sunLight.intensity = sunIntensity;
        // Only cast shadows when sun is sufficiently bright
        sunLight.castShadow = sunIntensity > 0.01;
    }
    if (moonLight) {
        moonLight.intensity = moonIntensity;
    }

    // Update visibility of sun/moon meshes based on altitude
    if(sunMesh) sunMesh.visible = sunY > -sunMesh.geometry.parameters.radius * 2; // Visible when above horizon
    if(moonMesh) moonMesh.visible = -sunY > -moonMesh.geometry.parameters.radius * 2; // Visible when sun is below horizon

    // Update stars opacity
    if (starsDiv) {
        starsDiv.style.opacity = starsOpacity;
    }
}
// Helper to format game time (0.0-1.0) into HH:MM string
function formatTime(time) {
    const hours = Math.floor(time * 24);
    const minutes = Math.floor((time * 24 * 60) % 60);
    return `${hours.toString().padStart(2, '0')}:${minutes.toString().padStart(2, '0')}`;
}


// --- Update Torch Animation ---
// Applies bobbing, flickering light, and flame animation
function updateTorchAnimation(delta, time) {
    if (!torchMesh || !torchLight || !flameMesh) return; // Safety check

    // Base position/rotation (reset potential bobbing from previous frame)
    const basePos = new THREE.Vector3(0.30, -0.25, -0.45);
    const baseRot = new THREE.Euler(0, -Math.PI / 16, Math.PI / 14);
    torchMesh.position.copy(basePos);
    torchMesh.rotation.copy(baseRot);

    // --- Viewmodel Bobbing ---
    // Check if player is moving significantly on the XZ plane or vertically
    const isMovingXZ = Math.abs(player.velocity.x) > 0.1 || Math.abs(player.velocity.z) > 0.1;
    const isMovingY = Math.abs(player.velocity.y) > 0.1;
    // Apply bobbing if walking on ground OR flying and moving
    const applyBob = (isMovingXZ && player.onGround) || (player.flyMode && (isMovingXZ || isMovingY));

    if (applyBob) {
        torchBobbingAngle += torchBobbingSpeed * delta;
        // Apply sinusoidal motion for bobbing
        torchMesh.position.y += Math.sin(torchBobbingAngle) * torchBobbingAmount; // Vertical bob
        torchMesh.position.x -= Math.cos(torchBobbingAngle * 0.5) * torchBobbingAmount * 0.5; // Slight horizontal sway
    } else {
        torchBobbingAngle = 0; // Reset angle when not moving
    }

    // --- Light Flicker ---
    const flicker = Math.sin(time * torchFlickerSpeed) * torchFlickerAmount;
    torchLight.intensity = torchBaseLightIntensity + flicker;

    // --- Flame Mesh Animation ---
    // Make flame scale and position flicker slightly
    const flameFlickerScale = 1.0 + Math.sin(time * torchFlickerSpeed * 0.8 + 0.5) * 0.1; // Scale Y
    const flameFlickerPosY = Math.sin(time * torchFlickerSpeed * 1.2 + 1.0) * 0.01; // Bob Y
    flameMesh.scale.y = flameFlickerScale;
    // Make flame position relative to light position (which is fixed relative to handle)
    flameMesh.position.y = torchLight.position.y + flameFlickerPosY;
}

// --- Update Torch Particles ---
// Updates particle positions, lifetimes, and resets expired particles
function updateTorchParticles(delta) {
    if (!particleSystem || !particleGeometry || !flameMesh) return; // Safety check

    const positions = particleGeometry.attributes.position.array;
    // Get current base Y position for spawning new particles (adjust for flame animation)
    const flameOriginY = flameMesh.position.y - flameMesh.geometry.parameters.radius * 0.5;

    for (let i = 0; i < particleCount; i++) {
        const i3 = i * 3;
        particleLifetimes[i] -= delta; // Decrease lifetime

        // --- Reset Particle if Lifetime Expired ---
        if (particleLifetimes[i] <= 0) {
            // Reset position to flame origin area
            positions[i3] = (Math.random() - 0.5) * particleSpawnRadius * 2;
            positions[i3 + 1] = flameOriginY + Math.random() * 0.05;
            positions[i3 + 2] = (Math.random() - 0.5) * particleSpawnRadius * 2;

            // Reset velocity
            particleVelocities[i].set(
                (Math.random() - 0.5) * particleVelocityVariance * 0.5,
                particleBaseVelocityY + Math.random() * particleVelocityVariance,
                (Math.random() - 0.5) * particleVelocityVariance * 0.5
            );

            // Reset lifetime
            particleLifetimes[i] = particleBaseLifetime + (Math.random() - 0.5) * particleLifetimeVariance * 2;

        } else { // --- Update Active Particle ---
            // Update position based on velocity
            positions[i3] += particleVelocities[i].x * delta;
            positions[i3 + 1] += particleVelocities[i].y * delta;
            positions[i3 + 2] += particleVelocities[i].z * delta;

            // Apply gravity
            particleVelocities[i].y -= particleGravity * delta;
        }
    }

    // Mark position attribute as needing update for the GPU
    particleGeometry.attributes.position.needsUpdate = true;
}


// --- Game Loop ---
function animate() {
    requestAnimationFrame(animate); // Schedule next frame

    // Ensure clock is ready before proceeding (important if init fails early)
    if (!clock) return;

    const delta = Math.min(clock.getDelta(), 0.05); // Get time since last frame, cap at 50ms to prevent physics jumps
    const time = clock.elapsedTime; // Total elapsed time

    // Update day/night cycle and related visuals
    updateAtmosphere(delta);

    // Update player movement and collision only if controls are locked
    if (controls && controls.isLocked === true) {

        // --- Calculate Movement Direction ---
        // Get input direction (forward/backward, left/right)
        player.direction.z = Number(moveForward) - Number(moveBackward);
        player.direction.x = Number(moveRight) - Number(moveLeft);
        player.direction.normalize(); // Ensure consistent speed diagonally

        // Get camera's forward and right vectors (on the XZ plane)
        const cameraDirection = new THREE.Vector3();
        controls.getDirection(cameraDirection); // Gets the look direction
        const forward = new THREE.Vector3(cameraDirection.x, 0, cameraDirection.z).normalize();
        const right = new THREE.Vector3().crossVectors(camera.up, forward).normalize(); // Right is up X forward (adjust if camera rolls)

        // Calculate target velocity based on input and camera direction
        const currentSpeed = player.flyMode ? player.flySpeed : player.speed;
        const targetVelocityXZ = new THREE.Vector3();
        targetVelocityXZ.addScaledVector(forward, player.direction.z); // Move along forward vector
        targetVelocityXZ.addScaledVector(right, player.direction.x); // Move along right vector

        if (targetVelocityXZ.lengthSq() > 0) { // Normalize only if there's input
            targetVelocityXZ.normalize().multiplyScalar(currentSpeed);
        }

        // Apply target velocity (instant change for responsive controls)
        player.velocity.x = targetVelocityXZ.x;
        player.velocity.z = targetVelocityXZ.z;

        // --- Vertical Movement & Gravity ---
        if (player.flyMode) {
            // Simple fly controls
            const verticalSpeed = player.flySpeed; // Use flySpeed for vertical too
            if (moveUp) player.velocity.y = verticalSpeed;
            else if (moveDown) player.velocity.y = -verticalSpeed;
            else player.velocity.y = 0; // Stop vertical movement if no input
            player.onGround = false; // Cannot be on ground while flying
        } else {
            // Apply gravity
            player.velocity.y -= gravity * delta;
            // Handle jumping
            if (moveUp && player.onGround) { // Can only jump if on ground
                player.velocity.y = player.jumpVelocity; // Set initial jump velocity
                player.onGround = false; // No longer on ground after jumping
            }
            // Note: moveDown (Shift) currently does nothing when not flying
        }

        // --- Collision Resolution (Simplified Axis Separation) ---
        const oldPosition = controls.getObject().position.clone();
        let newPosition = oldPosition.clone();

        // Move and check X axis
        newPosition.x += player.velocity.x * delta;
        if (checkCollision(newPosition)) {
            newPosition.x = oldPosition.x; // Revert X movement
            player.velocity.x = 0; // Stop X velocity
        }
        oldPosition.x = newPosition.x; // Update position for next axis check

        // Move and check Z axis
        newPosition.z += player.velocity.z * delta;
        if (checkCollision(newPosition)) {
            newPosition.z = oldPosition.z; // Revert Z movement
            player.velocity.z = 0; // Stop Z velocity
        }
        oldPosition.z = newPosition.z; // Update position

        // Move and check Y axis
        newPosition.y += player.velocity.y * delta;
        const verticalCollision = checkCollision(newPosition);
        player.onGround = false; // Assume not on ground unless collision below proves otherwise

        if (verticalCollision) {
            if (player.velocity.y <= 0) { // Colliding while moving down or stationary vertically
                // Snap to ground: find the block surface player landed on
                const intendedFeetY = newPosition.y - player.height;
                const snappedFeetY = Math.floor(intendedFeetY) + 1; // Top surface of block below feet
                newPosition.y = snappedFeetY + player.height + 0.001; // Place feet slightly above surface
                player.onGround = true; // Landed on ground
                player.velocity.y = 0; // Stop falling
            } else { // Colliding while moving up (hit ceiling)
                // Snap to ceiling: find the block surface player hit
                const intendedHeadY = newPosition.y;
                const snappedHeadY = Math.floor(intendedHeadY); // Bottom surface of block above head
                newPosition.y = snappedHeadY - 0.001; // Place head slightly below surface
                player.velocity.y = 0; // Stop rising
            }
        } else {
             // If not colliding vertically, but moving down & not flying, check if there's ground just below
            if (!player.flyMode && player.velocity.y <= 0) {
                if(checkCollision(newPosition, true)) { // Check slightly below feet
                     // This logic might need refinement if checkCollision(true) snaps position
                     // For now, we only set onGround if a downward collision actually happened above.
                }
            }
        }

        // Apply the final, collision-resolved position
        controls.getObject().position.copy(newPosition);
        player.position.copy(newPosition); // Keep player state synced

    } else if (player && player.velocity) { // If pointer not locked, gradually stop player movement
        player.velocity.x *= 0.9; // Apply damping
        player.velocity.z *= 0.9;
        // Don't damp Y velocity if not locked, allow falling to continue naturally
    }

    // Update torch animations (bobbing, flickering)
    // Check if torchMesh exists (might not if init failed)
    if (torchMesh) {
        updateTorchAnimation(delta, time);
    }
    // Update torch particles
    // Check if particleSystem exists
    if (particleSystem) {
        updateTorchParticles(delta);
    }

    // Load/unload chunks based on player position
    updateVisibleChunks(); // This should be safe even if controls/player aren't fully ready

    // Update Debug Info Display
    if (player && player.position && player.currentChunk && infoDiv) {
        const pos = player.position;
        infoDiv.textContent = `Pos: (${pos.x.toFixed(1)}, ${pos.y.toFixed(1)}, ${pos.z.toFixed(1)}) Chunk: ${player.currentChunk.x ?? 'N/A'},${player.currentChunk.z ?? 'N/A'} Fly: ${player.flyMode} Ground: ${player.onGround} Time: ${formatTime(gameTime)}`;
    }

    // Render the scene
    // Final safety check for core Three.js objects
    if (renderer && scene && camera) {
        renderer.render(scene, camera);
    }
}


// --- Start ---
// Wrap initialization in a try...catch to handle potential errors gracefully
try {
    init();
} catch(err) {
    console.error("Initialization failed:", err);
    // Display error message to the user
    const blocker = document.getElementById('blocker');
    const instructions = document.getElementById('instructions');
    if (blocker && instructions) {
        blocker.classList.add('error'); // Add error class for styling
        instructions.innerHTML = `<h2>Error</h2> Initialization failed. Check console (F12) for details.<br><pre>${err.message}\n${err.stack?.substring(0, 300)}...</pre>`; // Show error info
        blocker.style.display = 'flex'; // Ensure blocker is visible
    }
    // Clean up renderer canvas if it was created before error
    if (renderer && renderer.domElement && renderer.domElement.parentNode) {
        renderer.domElement.parentNode.removeChild(renderer.domElement);
    }
}