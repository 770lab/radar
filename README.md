# 📡 Radar

**https://770lab.com/radar/** — la carte de ceux qui sont là, en direct.

Chaque visiteur qui accepte la géolocalisation apparaît sur la carte de tous
les autres, tant que sa page reste ouverte. Tu fermes → tu disparais.
Rien n'est enregistré.

## Fonctionnalités

- **Carte live** (thème clair) : tout le monde en temps réel, avec pseudo,
  couleur et distance.
- **Se rejoindre** : clique sur une personne (marqueur ou pastille du bas) →
  un trait vous relie et un bandeau affiche la distance + le **temps estimé**,
  recalculé en direct à mesure que l'un ou l'autre se rapproche. La personne
  visée est prévenue (« X vient te rejoindre ») ; si vous vous sélectionnez
  mutuellement, le trait devient plein (« vous vous rejoignez »).

## Fonctionnement

- **Front** : statique (GitHub Pages), vanilla JS + **Google Maps JavaScript API**
  (carte, marqueurs custom via OverlayView, Places Autocomplete, Directions
  piéton). Clé Maps du projet `geo-loc-489602`, **verrouillée sur 770lab.com**
  (voir `js/config.js`). Firebase vendorisé dans `vendor/`.
- **Temps réel** : Firebase Realtime Database (`radar-770lab`, europe-west1),
  auth anonyme.
- **Présence** : `/presence/$pid` (une clé par onglet, champ `owner`=uid) avec
  `onDisconnect().remove()` (disparition auto à la fermeture), heartbeat 25 s,
  blip grisé après 75 s sans signe de vie, nettoyage des nœuds zombie après
  10 min. Le rendez-vous visé est publié dans le champ optionnel `target`.
- **Se rejoindre** : itinéraire piéton réel (Google Directions, mode marche)
  qui suit les rues ; distance + durée du trajet recalculées à mesure qu'on
  avance. Repli « à vol d'oiseau » (régression sur ~20 s) si l'itinéraire n'est
  pas encore prêt.
- **Point de test** : bouton ＋ → adresse (autocomplétion Google Places) → point
  « Test » local (jamais écrit en base) pour essayer le rendez-vous seul.

## Sécurité / vie privée

- Lecture de `/presence` réservée aux visiteurs authentifiés (l'app s'auth au
  chargement) : bloque le scraping anonyme. Écriture uniquement sur son propre
  nœud, schéma strictement validé et timestamp forcé côté serveur
  (`database.rules.json`).
- Position partagée uniquement après opt-in explicite, arrondie à ~11 m
  (4 décimales), jamais persistée au-delà de la session.
- Pseudos échappés avant insertion dans le DOM (pas de XSS via la DB).

## Développement

```bash
python3 -m http.server 8123   # puis http://localhost:8123
```

Déployer les règles RTDB après modification :

```bash
firebase deploy --only database --project radar-770lab
```

Le site se déploie tout seul : push sur `main` → GitHub Pages.
Penser à bumper `?v=N` sur `<script>`/`<link>` dans `index.html` après une
modif JS/CSS.
