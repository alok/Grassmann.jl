import 'katex/dist/katex.min.css';
import './styles/studio.css';
import { GrassmannStudioApp } from './ui/studioApp';

const root = document.getElementById('app');
if (!root) {
  throw new Error('Missing #app container in index.html');
}

const studio = new GrassmannStudioApp(root);

if (import.meta.hot) {
  import.meta.hot.dispose(() => studio.dispose());
}
