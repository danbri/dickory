import {mountWebMCP} from '../headless-webmcp.js';
mountWebMCP().catch(e=>console.warn('Linked Assurance native WebMCP registration failed:',String(e)));
